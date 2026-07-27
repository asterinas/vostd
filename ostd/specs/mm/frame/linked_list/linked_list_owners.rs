use core::marker::PhantomData;

use vstd::prelude::*;

use vstd::{atomic::*, seq_lib::*, set_lib::*, simple_pptr::*};
use vstd_extra::{
    cast_ptr::{Repr, ReprPtr},
    ownership::*,
};

use crate::specs::{
    arch::MAX_NR_PAGES,
    mm::frame::{
        mapping::{frame_to_index, max_meta_slots},
        meta_owners::*,
        meta_region_owners::MetaRegionOwners,
        unique::UniqueFrameOwner,
    },
};

use crate::mm::{
    Paddr,
    frame::{
        AnyFrameMeta, CursorMut, Link, LinkedList, MetaSlot,
        meta::{
            META_SLOT_SIZE, REF_COUNT_UNIQUE,
            mapping::{frame_to_meta, meta_to_frame},
        },
    },
    kspace::FRAME_METADATA_RANGE,
};

use super::*;

verus! {

pub struct MetaSlotSmall;

/// Representation of a link as stored in the metadata slot.
pub struct StoredLink {
    pub next: Option<Paddr>,
    pub prev: Option<Paddr>,
    pub slot: MetaSlotSmall,
}

pub tracked struct LinkInnerPerms<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
    pub storage: <M as Repr<MetaSlotSmall>>::ReprPerm,
    pub ghost next_ptr: Option<PPtr<MetaSlotStorage>>,
    pub ghost prev_ptr: Option<PPtr<MetaSlotStorage>>,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Repr<MetaSlotStorage> for Link<M> {
    type ReprPerm = LinkInnerPerms<M>;

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

    open spec fn to_repr_spec(self, perm: LinkInnerPerms<M>) -> (
        MetaSlotStorage,
        LinkInnerPerms<M>,
    ) {
        let (slot, storage) = self.meta.to_repr_spec(perm.storage);
        (
            MetaSlotStorage::FrameLink(
                StoredLink {
                    next: match self.next {
                        Some(ptr) => Some(ptr.ptr.addr()),
                        None => None,
                    },
                    prev: match self.prev {
                        Some(ptr) => Some(ptr.ptr.addr()),
                        None => None,
                    },
                    slot,
                },
            ),
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
                    Some(addr) => Some(ReprPtr { ptr: perm.next_ptr->0, _T: PhantomData }),
                    None => None,
                },
                prev: match link.prev {
                    Some(addr) => Some(ReprPtr { ptr: perm.prev_ptr->0, _T: PhantomData }),
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
    fn from_borrowed<'a>(
        r: &'a MetaSlotStorage,
        Tracked(perm): Tracked<&'a LinkInnerPerms<M>>,
    ) -> &'a Self {
        unimplemented!()
    }

    #[verifier::external_body]
    fn from_borrowed_mut<'a>(
        r: &'a mut MetaSlotStorage,
        Tracked(perm): Tracked<&'a mut LinkInnerPerms<M>>,
    ) -> &'a mut Self {
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
    pub ghost paddr: Paddr,
    pub ghost in_list: u64,
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
    pub repr_perms: Seq<LinkInnerPerms<M>>,
    pub ghost list_id: u64,
    pub ghost _marker: core::marker::PhantomData<M>,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Inv for LinkedListOwner<M> {
    open spec fn inv(self) -> bool {
        // Weakened (our change): an EMPTY list may carry `list_id == 0` (the
        // lazily-minted-id convention used by the list-store embedding); the
        // id is only constrained non-zero once the list is non-empty.
        &&& self.list.len() > 0 ==> self.list_id != 0
        &&& self.repr_perms.len() == self.list.len()
        &&& forall|i: int| 0 <= i < self.list.len() ==> self.inv_at(i)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedListOwner<M> {
    pub open spec fn meta_addr_at(self, regions: MetaRegionOwners, i: int) -> usize {
        regions.slots[self.slot_index_at(i)].addr()
    }

    pub open spec fn meta_pptr_at(self, regions: MetaRegionOwners, i: int) -> PPtr<MetaSlot> {
        regions.slots[self.slot_index_at(i)].pptr()
    }

    /// Per-link structural invariant: the link's own `inv()` holds and its
    /// `in_list` tag matches the list's `list_id`. The per-link metadata facts
    /// (perm wf/is_init/pointer wiring) are tracked via `relate_region_at`
    /// against the global `MetaRegionOwners`, NOT through this predicate.
    pub open spec fn inv_at(self, i: int) -> bool {
        &&& self.list[i].inv()
        &&& self.list[i].in_list == self.list_id
    }

    /// The region slot index keyed by the `i`-th link's meta-slot address.
    pub open spec fn slot_index_at(self, i: int) -> int {
        frame_to_index(meta_to_frame(self.list[i].paddr))
    }

    pub open spec fn meta_wf_at(self, regions: MetaRegionOwners, i: int) -> bool {
        let idx = self.slot_index_at(i);
        typed_meta_wf::<Link<M>>(
            regions.slots[idx],
            regions.slot_owners[idx].inner_perms.storage,
            self.repr_perms[i],
        )
    }

    pub open spec fn meta_value_at(self, regions: MetaRegionOwners, i: int) -> Link<M>
        recommends
            self.meta_wf_at(regions, i),
    {
        let idx = self.slot_index_at(i);
        typed_meta_value::<Link<M>>(
            regions.slot_owners[idx].inner_perms.storage,
            self.repr_perms[i],
        )
    }

    /// The per-link invariant expressed directly over the region-owned slot and
    /// storage permissions plus the list-owned representation permission.
    #[verifier::opaque]
    pub open spec fn relate_region_at(self, regions: MetaRegionOwners, i: int) -> bool {
        let idx = self.slot_index_at(i);
        let value = self.meta_value_at(regions, i);
        &&& regions.slots.contains_key(idx)
        &&& regions.slot_owners.contains_key(idx)
        &&& regions.slots[idx].addr() == self.list[i].paddr
        &&& regions.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
        &&& regions.slot_owners[idx].usage is Frame
        &&& regions.slot_owners[idx].inner_perms.in_list.value() == self.list_id
        &&& self.meta_wf_at(regions, i)
        &&& regions.slots[idx].addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= regions.slots[idx].addr() < FRAME_METADATA_RANGE.start
            + MAX_NR_PAGES * META_SLOT_SIZE
        &&& value.wf(self.list[i])
        &&& i == 0 <==> value.prev is None
        &&& i == self.list.len() - 1 <==> value.next is None
        &&& 0 < i ==> {
            &&& value.prev is Some
            &&& value.prev->0.addr() == self.meta_addr_at(regions, i - 1)
        }
        &&& i < self.list.len() - 1 ==> {
            &&& value.next is Some
            &&& value.next->0.addr() == self.meta_addr_at(regions, i + 1)
        }
        &&& self.list[i].inv()
        &&& self.list[i].in_list == self.list_id
    }

    /// The list-wide region relation: every link satisfies `relate_region_at`,
    /// and distinct list positions map to distinct region slot indices (so a
    /// frame appears at most once — required by the borrow model, where link
    /// edits mutate `regions.slots[slot_index_at(i)]` and must not alias).
    pub open spec fn relate_region(self, regions: MetaRegionOwners) -> bool {
        &&& self.repr_perms.len() == self.list.len()
        &&& forall|i: int|
            #![trigger self.list[i]]
            0 <= i < self.list.len() ==> self.relate_region_at(regions, i)
        &&& forall|i: int, j: int|
            #![trigger self.slot_index_at(i), self.slot_index_at(j)]
            0 <= i < self.list.len() && 0 <= j < self.list.len() && i != j ==> self.slot_index_at(i)
                != self.slot_index_at(j)
        &&& self.list.len() > 0 ==> self.list_id != 0
    }

    /// Pigeonhole bound: the list is no longer than the number of meta slots.
    /// Each link occupies a region slot (`relate_region_at` ⟹
    /// `slots.contains_key(slot_index_at(i))`, and `regions.inv()` ⟹
    /// `slot_index_at(i) < max_meta_slots()`), and distinct positions occupy
    /// distinct slots (`relate_region`'s injectivity). So the positions inject
    /// into `[0, max_meta_slots())` and the length is capped by it.
    pub proof fn length_le_max_meta_slots(self, regions: MetaRegionOwners)
        requires
            self.relate_region(regions),
            regions.inv(),
        ensures
            self.list.len() <= max_meta_slots(),
    {
        let idxs = Seq::new(self.list.len(), |i: int| self.slot_index_at(i));

        idxs.unique_seq_to_set();

        let bound = set_int_range(0, max_meta_slots());
        assert(idxs.to_set().subset_of(bound)) by {
            assert forall|x: int|
                #![trigger idxs.to_set().contains(x)]
                idxs.to_set().contains(x) implies bound.contains(x) by {
                let i = choose|i: int| 0 <= i < idxs.len() && idxs[i] == x;
                self.relate_region_at_facts(regions, i);
                // `regions.inv()`: `contains_key(slot_index_at(i)) ⟹ < max_meta_slots()`.
            }
        }
        lemma_int_range(0, max_meta_slots());
        lemma_len_subset(idxs.to_set(), bound);
    }

    /// The list counter can never saturate: its length is capped by
    /// `max_meta_slots()` (see [`Self::length_le_max_meta_slots`]), which is far
    /// below `usize::MAX`. Lets `insert_before` discharge the `size + 1`
    /// overflow check without a caller-supplied non-fullness precondition.
    pub proof fn length_lt_usize_max(self, regions: MetaRegionOwners)
        requires
            self.relate_region(regions),
            regions.inv(),
        ensures
            self.list.len() < usize::MAX,
    {
        self.length_le_max_meta_slots(regions);
    }

    /// Unfolds the opaque `relate_region_at` ONCE and exposes its clauses.
    /// `relate_region_at` is opaque to avoid quantifier explosion at use sites;
    /// this lemma localizes the reveal so callers get
    /// the facts at a single index without re-exploding the SMT context.
    pub proof fn relate_region_at_facts(self, regions: MetaRegionOwners, i: int)
        requires
            self.relate_region_at(regions, i),
        ensures
            ({
                let idx = self.slot_index_at(i);
                let value = self.meta_value_at(regions, i);
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots[idx].addr() == self.list[i].paddr
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                &&& regions.slot_owners[idx].usage is Frame
                &&& regions.slot_owners[idx].inner_perms.in_list.value() == self.list_id
                &&& self.meta_wf_at(regions, i)
                &&& regions.slots[idx].addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= regions.slots[idx].addr()
                    < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE
                &&& value.wf(self.list[i])
                &&& (i == 0 <==> value.prev is None)
                &&& (i == self.list.len() - 1 <==> value.next is None)
                &&& (0 < i ==> {
                    &&& value.prev is Some
                    &&& value.prev->0.addr() == self.meta_addr_at(regions, i - 1)
                })
                &&& (i < self.list.len() - 1 ==> {
                    &&& value.next is Some
                    &&& value.next->0.addr() == self.meta_addr_at(regions, i + 1)
                })
                &&& self.list[i].inv()
                &&& self.list[i].in_list == self.list_id
            }),
    {
        reveal(LinkedListOwner::relate_region_at);
    }

    /// Constructor (inverse of [`relate_region_at_facts`]): establishes the
    /// opaque `relate_region_at` from its unfolded clauses. Used by the pop/
    /// insert "surgery" proofs, which assemble each clause for the new list and
    /// then fold them back into the opaque predicate.
    pub proof fn relate_region_at_from_clauses(self, regions: MetaRegionOwners, i: int)
        requires
            ({
                let idx = self.slot_index_at(i);
                let value = self.meta_value_at(regions, i);
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners.contains_key(idx)
                &&& self.repr_perms.len() == self.list.len()
                &&& regions.slots[idx].addr() == self.list[i].paddr
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                &&& regions.slot_owners[idx].usage is Frame
                &&& regions.slot_owners[idx].inner_perms.in_list.value() == self.list_id
                &&& self.meta_wf_at(regions, i)
                &&& regions.slots[idx].addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= regions.slots[idx].addr()
                    < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE
                &&& value.wf(self.list[i])
                &&& (i == 0 <==> value.prev is None)
                &&& (i == self.list.len() - 1 <==> value.next is None)
                &&& (0 < i ==> {
                    &&& value.prev is Some
                    &&& value.prev->0.addr() == self.meta_addr_at(regions, i - 1)
                })
                &&& (i < self.list.len() - 1 ==> {
                    &&& value.next is Some
                    &&& value.next->0.addr() == self.meta_addr_at(regions, i + 1)
                })
                &&& self.list[i].inv()
                &&& self.list[i].in_list == self.list_id
            }),
        ensures
            self.relate_region_at(regions, i),
    {
        reveal(LinkedListOwner::relate_region_at);
    }

    /// `relate_region` is preserved under a region change that doesn't touch
    /// any of the list's slots. Used by `LinkedList::drop`'s loop body: after
    /// `take_current` pops position 0, the popped slot is dropped via
    /// `frame.drop`, which only modifies `regions.slot_owners[cur_idx]` and
    /// leaves `regions.slots` fully untouched. Since the cursor's remaining
    /// list never contains `cur_idx` (distinctness on the original list),
    /// `relate_region` carries through.
    pub proof fn relate_region_preserved_external_change(
        self,
        regions1: MetaRegionOwners,
        regions2: MetaRegionOwners,
    )
        requires
            self.relate_region(regions1),
            regions2.slots == regions1.slots,
            forall|i: int|
                #![trigger self.list[i]]
                0 <= i < self.list.len() ==> {
                    let idx = self.slot_index_at(i);
                    &&& regions2.slot_owners.contains_key(idx)
                    &&& regions2.slot_owners[idx] == regions1.slot_owners[idx]
                },
        ensures
            self.relate_region(regions2),
    {
        let llen = self.list.len() as int;
        assert forall|k: int|
            #![trigger self.relate_region_at(regions2, k)]
            0 <= k < llen implies self.relate_region_at(regions2, k) by {
            let _ = self.list[k];
            self.relate_region_at_facts(regions1, k);
            self.relate_region_at_from_clauses(regions2, k);
        }
    }

    /// The list-rewiring "surgery" for popping the element at index `n`: given
    /// the entry invariant `old.relate_region(r0)` and a characterization of the
    /// post-pop region `fr` (every surviving slot keeps its local facts and
    /// pointers, except the two neighbors whose `next`/`prev` were rewired to
    /// bridge the gap), the shrunk list `new` satisfies `relate_region(fr)`.
    ///
    /// New position `k` maps to old position `p = (k < n ? k : k+1)`; the
    /// neighbor of `k` maps to `p ± 1` except across the cut (new position `n-1`
    /// reaches old `n+1`, new position `n` reaches old `n-1`), which is exactly
    /// where the body rewired the link pointers.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(60)]
    pub proof fn pop_preserves_relate_region(
        old: LinkedListOwner<M>,
        r0: MetaRegionOwners,
        new: LinkedListOwner<M>,
        fr: MetaRegionOwners,
        n: int,
    )
        requires
            0 <= n < old.list.len(),
            old.relate_region(r0),
            new.list == old.list.remove(n),
            new.repr_perms.len() == new.list.len(),
            new.list_id == old.list_id,
            forall|p: int|
                #![trigger old.slot_index_at(p)]
                (0 <= p < old.list.len() && p != n) ==> ({
                    let i = old.slot_index_at(p);
                    let np = if p < n {
                        p
                    } else {
                        p - 1
                    };
                    let fp = typed_meta_value::<Link<M>>(
                        fr.slot_owners[i].inner_perms.storage,
                        new.repr_perms[np],
                    );
                    &&& fr.slots.contains_key(i)
                    &&& fr.slot_owners.contains_key(i)
                    &&& fr.slots[i].addr() == old.list[p].paddr
                    &&& fr.slots[i].pptr() == r0.slots[i].pptr()
                    &&& fr.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                    &&& fr.slot_owners[i].usage is Frame
                    &&& fr.slot_owners[i].inner_perms.in_list.value() == new.list_id
                    &&& typed_meta_wf::<Link<M>>(
                        fr.slots[i],
                        fr.slot_owners[i].inner_perms.storage,
                        new.repr_perms[np],
                    )
                    &&& fr.slots[i].addr() % META_SLOT_SIZE == 0
                    &&& FRAME_METADATA_RANGE.start <= fr.slots[i].addr()
                        < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE
                    &&& (p == n - 1 ==> fp.next == old.meta_value_at(r0, n).next)
                    &&& (p != n - 1 ==> fp.next == old.meta_value_at(r0, p).next)
                    &&& (p == n + 1 ==> fp.prev == old.meta_value_at(r0, n).prev)
                    &&& (p != n + 1 ==> fp.prev == old.meta_value_at(r0, p).prev)
                }),
        ensures
            new.relate_region(fr),
    {
        let nlen = new.list.len() as int;

        assert forall|k: int| #![trigger new.slot_index_at(k)] 0 <= k < nlen implies {
            let p = if k < n {
                k
            } else {
                k + 1
            };
            &&& new.list[k] == old.list[p]
            &&& new.slot_index_at(k) == old.slot_index_at(p)
        } by {}

        assert forall|a: int, b: int|
            #![trigger new.slot_index_at(a), new.slot_index_at(b)]
            0 <= a < nlen && 0 <= b < nlen && a != b implies new.slot_index_at(a)
            != new.slot_index_at(b) by {
            let pa = if a < n {
                a
            } else {
                a + 1
            };
            let pb = if b < n {
                b
            } else {
                b + 1
            };
        }

        assert forall|m: int| #![trigger new.meta_addr_at(fr, m)] 0 <= m < nlen implies {
            let pm = if m < n {
                m
            } else {
                m + 1
            };
            &&& new.meta_addr_at(fr, m) == old.meta_addr_at(r0, pm)
            &&& new.meta_pptr_at(fr, m) == old.meta_pptr_at(r0, pm)
        } by {
            let pm = if m < n {
                m
            } else {
                m + 1
            };
            let _ = old.list[pm];
            old.relate_region_at_facts(r0, pm);
        }

        assert forall|k: int|
            #![trigger new.relate_region_at(fr, k)]
            0 <= k < nlen implies new.relate_region_at(fr, k) by {
            let p = if k < n {
                k
            } else {
                k + 1
            };
            let _ = old.list[p];
            old.relate_region_at_facts(r0, p);
            let _ = old.list[n];
            old.relate_region_at_facts(r0, n);
            if p - 1 >= 0 {
                let _ = old.list[p - 1];
                old.relate_region_at_facts(r0, p - 1);
            }
            if p + 1 < old.list.len() {
                let _ = old.list[p + 1];
                old.relate_region_at_facts(r0, p + 1);
            }
            if n - 1 >= 0 {
                let _ = old.list[n - 1];
                old.relate_region_at_facts(r0, n - 1);
            }
            if n + 1 < old.list.len() {
                old.relate_region_at_facts(r0, n + 1);
            }
            new.relate_region_at_from_clauses(fr, k);
        }

    }

    /// The list-rewiring "surgery" for inserting `link` before index `n`
    /// (`0 <= n <= old.list.len()`): given the entry `relate_region` and a
    /// per-slot characterization of the post-insert region `fr`, the longer list
    /// `new = old.list.insert(n, link)` satisfies `relate_region(fr)`.
    ///
    /// New position `k` maps to old position `k` (k<n), is the inserted link
    /// (k==n), or maps to old `k-1` (k>n). The inserted link sits at slot
    /// `ins = new.slot_index_at(n)`; its `prev`/`next` point to old `n-1`/`n`
    /// (or `None` at the ends), and old `n-1`'s `next` / old `n`'s `prev` are
    /// rewired to point at the inserted link. Mirror of
    /// [`pop_preserves_relate_region`].
    #[verifier::spinoff_prover]
    #[verifier::rlimit(120)]
    pub proof fn insert_preserves_relate_region(
        old: LinkedListOwner<M>,
        r0: MetaRegionOwners,
        new: LinkedListOwner<M>,
        fr: MetaRegionOwners,
        n: int,
        link: LinkOwner,
    )
        requires
            0 <= n <= old.list.len(),
            old.relate_region(r0),
            new.list == old.list.insert(n, link),
            new.repr_perms.len() == new.list.len(),
            new.list_id != 0,
            old.list.len() > 0 ==> new.list_id == old.list_id,
            link.in_list == new.list_id,
            forall|p: int|
                #![trigger old.slot_index_at(p)]
                (0 <= p < old.list.len()) ==> old.slot_index_at(p) != new.slot_index_at(n),
            ({
                let ins = new.slot_index_at(n);
                let fpn = new.meta_value_at(fr, n);
                &&& fr.slots.contains_key(ins)
                &&& fr.slot_owners.contains_key(ins)
                &&& fr.slots[ins].addr() == link.paddr
                &&& fr.slot_owners[ins].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                &&& fr.slot_owners[ins].usage is Frame
                &&& fr.slot_owners[ins].inner_perms.in_list.value() == new.list_id
                &&& new.meta_wf_at(fr, n)
                &&& fr.slots[ins].addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= fr.slots[ins].addr() < FRAME_METADATA_RANGE.start
                    + MAX_NR_PAGES * META_SLOT_SIZE
                &&& (n == 0 <==> fpn.prev is None)
                &&& (n == old.list.len() <==> fpn.next is None)
                &&& (n > 0 ==> {
                    &&& fpn.prev is Some
                    &&& fpn.prev->0.addr() == old.list[n - 1].paddr
                    &&& fpn.prev->0.ptr.addr() == r0.slots[old.slot_index_at(n - 1)].pptr().addr()
                })
                &&& (n < old.list.len() ==> {
                    &&& fpn.next is Some
                    &&& fpn.next->0.addr() == old.list[n].paddr
                    &&& fpn.next->0.ptr.addr() == r0.slots[old.slot_index_at(n)].pptr().addr()
                })
            }),
            forall|p: int|
                #![trigger old.slot_index_at(p)]
                (0 <= p < old.list.len()) ==> ({
                    let i = old.slot_index_at(p);
                    let ins = new.slot_index_at(n);
                    let np = if p < n {
                        p
                    } else {
                        p + 1
                    };
                    let fp = new.meta_value_at(fr, np);
                    &&& fr.slots.contains_key(i)
                    &&& fr.slot_owners.contains_key(i)
                    &&& fr.slots[i].addr() == old.list[p].paddr
                    &&& fr.slots[i].pptr() == r0.slots[i].pptr()
                    &&& fr.slot_owners[i].inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                    &&& fr.slot_owners[i].usage is Frame
                    &&& fr.slot_owners[i].inner_perms.in_list.value() == new.list_id
                    &&& new.meta_wf_at(fr, np)
                    &&& fr.slots[i].addr() % META_SLOT_SIZE == 0
                    &&& FRAME_METADATA_RANGE.start <= fr.slots[i].addr()
                        < FRAME_METADATA_RANGE.start + MAX_NR_PAGES * META_SLOT_SIZE
                    &&& (p == n - 1 ==> {
                        &&& fp.next is Some
                        &&& fp.next->0.addr() == link.paddr
                        &&& fp.next->0.ptr.addr() == fr.slots[ins].pptr().addr()
                    })
                    &&& (p != n - 1 ==> fp.next == old.meta_value_at(r0, p).next)
                    &&& (p == n ==> {
                        &&& fp.prev is Some
                        &&& fp.prev->0.addr() == link.paddr
                        &&& fp.prev->0.ptr.addr() == fr.slots[ins].pptr().addr()
                    })
                    &&& (p != n ==> fp.prev == old.meta_value_at(r0, p).prev)
                }),
        ensures
            new.relate_region(fr),
    {
        let nlen = new.list.len() as int;
        let ins = new.slot_index_at(n);

        assert forall|k: int| #![trigger new.slot_index_at(k)] 0 <= k < nlen implies ({
            &&& (k < n ==> new.list[k] == old.list[k] && new.slot_index_at(k) == old.slot_index_at(
                k,
            ))
            &&& (k == n ==> new.list[k] == link && new.slot_index_at(k) == ins)
            &&& (k > n ==> new.list[k] == old.list[k - 1] && new.slot_index_at(k)
                == old.slot_index_at(k - 1))
        }) by {}

        assert forall|a: int, b: int|
            #![trigger new.slot_index_at(a), new.slot_index_at(b)]
            0 <= a < nlen && 0 <= b < nlen && a != b implies new.slot_index_at(a)
            != new.slot_index_at(b) by {}

        assert forall|m: int| #![trigger new.meta_addr_at(fr, m)] 0 <= m < nlen implies ({
            &&& (m < n ==> new.meta_addr_at(fr, m) == old.meta_addr_at(r0, m) && new.meta_pptr_at(
                fr,
                m,
            ) == old.meta_pptr_at(r0, m))
            &&& (m > n ==> new.meta_addr_at(fr, m) == old.meta_addr_at(r0, m - 1)
                && new.meta_pptr_at(fr, m) == old.meta_pptr_at(r0, m - 1))
        }) by {
            if m < n {
                let _ = old.list[m];
                old.relate_region_at_facts(r0, m);
            }
            if m > n {
                let _ = old.list[m - 1];
                old.relate_region_at_facts(r0, m - 1);
            }
        }

        assert forall|k: int|
            #![trigger new.relate_region_at(fr, k)]
            0 <= k < nlen implies new.relate_region_at(fr, k) by {
            if k < n {
                let _ = old.list[k];
                old.relate_region_at_facts(r0, k);
            }
            if k > n {
                let _ = old.list[k - 1];
                old.relate_region_at_facts(r0, k - 1);
            }
            if n - 1 >= 0 && n - 1 < old.list.len() {
                let _ = old.list[n - 1];
                old.relate_region_at_facts(r0, n - 1);
            }
            if n >= 0 && n < old.list.len() {
                let _ = old.list[n];
                old.relate_region_at_facts(r0, n);
            }
            new.relate_region_at_from_clauses(fr, k);
        }

        // `new` has `old.len + 1 ≥ 1 > 0` elements and a non-zero id by hypothesis.
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
        if owners.len() > 0 {
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
    /// view_helper(s.remove(i)) == view_helper(s).remove(i)
    pub proof fn view_helper_remove(owners: Seq<LinkOwner>, i: int)
        requires
            0 <= i < owners.len(),
        ensures
            Self::view_helper(owners.remove(i)) == Self::view_helper(owners).remove(i),
    {
        Self::view_preserves_len(owners);
        Self::view_preserves_len(owners.remove(i));
        assert forall|j: int|
            0 <= j < Self::view_helper(owners.remove(i)).len() implies Self::view_helper(
            owners.remove(i),
        )[j] == Self::view_helper(owners).remove(i)[j] by {
            Self::view_helper_index(owners.remove(i), j);
            if j < i {
                Self::view_helper_index(owners, j);
            } else {
                Self::view_helper_index(owners, j + 1);
            }
        };
    }

    /// Proves that view_helper commutes with insert:
    /// view_helper(s.insert(i, v)) == view_helper(s).insert(i, v.view())
    pub proof fn view_helper_insert(owners: Seq<LinkOwner>, i: int, v: LinkOwner)
        requires
            0 <= i <= owners.len(),
        ensures
            Self::view_helper(owners.insert(i, v)) == Self::view_helper(owners).insert(i, v.view()),
    {
        Self::view_preserves_len(owners);
        Self::view_preserves_len(owners.insert(i, v));
        assert forall|j: int|
            0 <= j < Self::view_helper(
                owners.insert(i, v),
            ).len() implies #[trigger] Self::view_helper(owners.insert(i, v))[j]
            == Self::view_helper(owners).insert(i, v.view())[j] by {
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
    /// `list`, so its `inv()` holds vacuously. Used by drop-style call sites
    /// that need to feed an owned `LinkedListOwner` to a downstream API while
    /// themselves only having a `&mut` to it.
    #[verifier::external_body]
    pub proof fn tracked_take(tracked owner: &mut Self) -> (tracked res: Self)
        ensures
            res == *old(owner),
            final(owner).list == Seq::<LinkOwner>::empty(),
            final(owner).repr_perms == Seq::<LinkInnerPerms<M>>::empty(),
            final(owner).inv(),
    {
        unimplemented!()
    }

    /// Discard a logically-empty `LinkedListOwner`. Sound because such an
    /// owner has an empty `list` and claims no external permissions (the
    /// borrow model parks all permissions in `MetaRegionOwners`).
    #[verifier::external_body]
    pub proof fn tracked_destroy_empty(tracked self)
        requires
            self.list =~= Seq::<LinkOwner>::empty(),
            self.repr_perms =~= Seq::<LinkInnerPerms<M>>::empty(),
    {
        unimplemented!()
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> OwnerOf for LinkedList<M> {
    type Owner = LinkedListOwner<M>;

    /// Structural well-formedness of the LinkedList against its owner: size,
    /// list_id, and front/back addresses match. The per-link pointer-permission
    /// facts (pptr/ptr equality against the front/back) live in `wf_region`,
    /// which sources them from `MetaRegionOwners`.
    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& self.front is None <==> owner.list.len() == 0
        &&& self.back is None <==> owner.list.len() == 0
        &&& owner.list.len() > 0 ==> self.front is Some && self.front->0.addr()
            == owner.list[0].paddr && self.back is Some && self.back->0.addr()
            == owner.list[owner.list.len() - 1].paddr
        &&& self.size == owner.list.len()
        &&& self.list_id == owner.list_id
    }
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
    pub ghost index: int,
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

    /// Structural well-formedness: `current` matches the link at `index`'s
    /// address. Pointer-permission facts (pptr/ptr equality) are stated in
    /// `wf_region` over the region-owned slot pointers.
    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& 0 <= owner.index < owner.length() ==> self.current.is_some() && self.current->0.addr()
            == owner.list_own.list[owner.index].paddr
        &&& owner.index == owner.list_own.list.len() ==> self.current.is_none()
        &&& (*self.list).wf(owner.list_own)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
    /// Region-based analog of [`LinkedList::wf`]: the front/back pointer facts
    /// are stated directly over the region-owned slot pointers.
    pub open spec fn wf_region(self, owner: LinkedListOwner<M>, regions: MetaRegionOwners) -> bool {
        &&& self.front is None <==> owner.list.len() == 0
        &&& self.back is None <==> owner.list.len() == 0
        &&& owner.list.len() > 0 ==> self.front is Some && self.front->0.addr()
            == owner.list[0].paddr && owner.meta_pptr_at(regions, 0).addr() == self.front->0.addr()
            && self.back is Some && self.back->0.addr() == owner.list[owner.list.len() - 1].paddr
            && owner.meta_pptr_at(regions, owner.list.len() - 1).addr() == self.back->0.addr()
        &&& self.size == owner.list.len()
        &&& self.list_id == owner.list_id
    }
}

impl<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>> CursorMut<'a, M> {
    /// Region-based analog of [`CursorMut::wf`]: the current-link pointer facts
    /// are stated over the corresponding region-owned slot pointer.
    pub open spec fn wf_region(self, owner: CursorOwner<M>, regions: MetaRegionOwners) -> bool {
        &&& 0 <= owner.index < owner.length() ==> self.current.is_some() && self.current->0.addr()
            == owner.list_own.list[owner.index].paddr && owner.list_own.meta_pptr_at(
            regions,
            owner.index,
        ).addr() == self.current->0.addr()
        &&& owner.index == owner.list_own.list.len() ==> self.current.is_none()
        &&& (*self.list).wf_region(owner.list_own, regions)
    }
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

    /// Region-based analog of [`CursorOwner::inv`]: replaces `list_own.inv()`
    /// (over the owned `perms`) with `list_own.relate_region(regions)` (over
    /// the region permissions).
    pub open spec fn wf_with_region(self, regions: MetaRegionOwners) -> bool {
        &&& 0 <= self.index <= self.length()
        &&& self.list_own.relate_region(regions)
    }

    pub open spec fn current(self) -> Option<LinkOwner> {
        if 0 <= self.index < self.length() {
            Some(self.list_own.list[self.index])
        } else {
            None
        }
    }

    pub open spec fn list_insert(
        cursor: Self,
        link: LinkOwner,
        repr_perm: LinkInnerPerms<M>,
        list_id: u64,
    ) -> (Self, LinkOwner)
        recommends
            list_id != 0,
            0 <= cursor.index <= cursor.list_own.list.len(),
            cursor.list_own.repr_perms.len() == cursor.list_own.list.len(),
            cursor.list_own.list.len() > 0 ==> list_id == cursor.list_own.list_id,
    {
        let link = LinkOwner { paddr: link.paddr, in_list: list_id };
        (
            Self {
                list_own: LinkedListOwner::<M> {
                    list: cursor.list_own.list.insert(cursor.index, link),
                    repr_perms: cursor.list_own.repr_perms.insert(cursor.index, repr_perm),
                    list_id,
                    _marker: PhantomData,
                },
                index: cursor.index + 1,
            },
            link,
        )
    }

    /// Tracked update to the cursor's owner state when a new link is inserted
    /// before the current position. The inserted `link`'s `paddr` is unchanged
    /// and its `in_list` is stamped with `list_id` — the (non-zero) id the
    /// concrete `lazy_get_id` resolved. The cursor's list gains `link` at
    /// `old.index`, adopts `list_id` (which equals the old id when that was
    /// already non-zero), and `index` advances by one. In the borrow model, the
    /// link's tracked permission remains parked in `MetaRegionOwners.slots`;
    /// this axiom doesn't need to take or carry a perm.
    pub proof fn tracked_list_insert(
        tracked cursor: &mut Self,
        tracked link: &mut LinkOwner,
        tracked repr_perm: LinkInnerPerms<M>,
        list_id: u64,
    )
        requires
            list_id != 0,
            0 <= old(cursor).index <= old(cursor).list_own.list.len(),
            old(cursor).list_own.repr_perms.len() == old(cursor).list_own.list.len(),
            old(cursor).list_own.list.len() > 0 ==> list_id == old(cursor).list_own.list_id,
            old(cursor).list_own.list_id != 0 ==> list_id == old(cursor).list_own.list_id,
        ensures
            ({
                let res = Self::list_insert(*old(cursor), *old(link), repr_perm, list_id);

                res.0 == *final(cursor) && res.1 == *final(link)
            }),
    {
        let ghost idx = cursor.index;
        let ghost link_paddr = link.paddr;
        let tracked list_entry = LinkOwner { paddr: link_paddr, in_list: list_id };

        cursor.list_own.list.tracked_insert(idx, list_entry);
        cursor.list_own.repr_perms.tracked_insert(idx, repr_perm);
        cursor.list_own.list_id = list_id;
        cursor.index = idx + 1;
        *link = LinkOwner { paddr: link_paddr, in_list: list_id };
    }

    pub open spec fn front_owner(list_own: LinkedListOwner<M>) -> Self {
        CursorOwner::<M> { list_own: list_own, index: 0 }
    }

    pub open spec fn cursor_mut_at_owner(list_own: LinkedListOwner<M>, index: int) -> Self {
        CursorOwner::<M> { list_own: list_own, index: index }
    }

    pub proof fn tracked_cursor_mut_at_owner(
        tracked list_own: LinkedListOwner<M>,
        index: int,
    ) -> tracked Self
        returns
            Self::cursor_mut_at_owner(list_own, index),
    {
        let tracked res = CursorOwner::<M> { list_own, index };
        res
    }

    pub proof fn tracked_front_owner(tracked list_own: LinkedListOwner<M>) -> tracked Self
        returns
            Self::front_owner(list_own),
    {
        let tracked res = CursorOwner::<M> { list_own, index: 0 };
        res
    }

    pub open spec fn back_owner(list_own: LinkedListOwner<M>) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            index: if list_own.list.len() > 0 {
                list_own.list.len() - 1
            } else {
                0
            },
        }
    }

    #[verifier::external_body]
    pub proof fn tracked_back_owner(list_own: LinkedListOwner<M>) -> (tracked res: Self)
        ensures
            res == Self::back_owner(list_own),
    {
        CursorOwner::<M> {
            list_own: list_own,
            index: if list_own.list.len() > 0 {
                list_own.list.len() - 1
            } else {
                0
            },
        }
    }

    pub open spec fn ghost_owner(list_own: LinkedListOwner<M>) -> Self {
        CursorOwner::<M> { list_own: list_own, index: list_own.list.len() as int }
    }

    #[verifier::external_body]
    pub proof fn tracked_ghost_owner(list_own: LinkedListOwner<M>) -> (tracked res: Self)
        ensures
            res == Self::ghost_owner(list_own),
    {
        CursorOwner::<M> { list_own: list_own, index: list_own.list.len() as int }
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> UniqueFrameOwner<Link<M>> {
    pub open spec fn frame_link_inv(&self, regions: MetaRegionOwners) -> bool {
        &&& self.meta_value(regions).prev is None
        &&& self.meta_value(regions).next is None
        &&& self.meta_own.paddr == regions.slots[self.slot_index].addr()
        &&& regions.slot_owners[self.slot_index].inner_perms.in_list.value() == 0
    }
}

} // verus!
