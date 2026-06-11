use vstd::atomic::*;
use vstd::cell;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::set_lib::*;
use vstd::simple_pptr::*;

use vstd::std_specs::convert::{FromSpec, FromSpecImpl};
use vstd_extra::cast_ptr::{Repr, ReprPtr};
use vstd_extra::ownership::*;

use core::marker::PhantomData;

use super::*;
use crate::mm::Paddr;
use crate::mm::frame::{AnyFrameMeta, CursorMut, Link, LinkedList, MetaSlot};
use crate::specs::arch::kspace::FRAME_METADATA_RANGE;
use crate::specs::arch::mm::MAX_NR_PAGES;
use crate::specs::mm::frame::mapping::{
    META_SLOT_SIZE, frame_to_index, max_meta_slots, meta_to_frame_spec,
};
use crate::specs::mm::frame::meta_owners::*;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
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
                    Some(addr) => Some(ReprPtr { ptr: perm.next_ptr.unwrap(), _T: PhantomData }),
                    None => None,
                },
                prev: match link.prev {
                    Some(addr) => Some(ReprPtr { ptr: perm.prev_ptr.unwrap(), _T: PhantomData }),
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
    pub list_id: u64,
    pub _marker: core::marker::PhantomData<M>,
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> Inv for LinkedListOwner<M> {
    open spec fn inv(self) -> bool {
        &&& self.list_id != 0
        &&& forall|i: int| 0 <= i < self.list.len() ==> self.inv_at(i)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedListOwner<M> {
    /// Per-link structural invariant: the link's own `inv()` holds and its
    /// `in_list` tag matches the list's `list_id`. The per-link metadata facts
    /// (perm wf/is_init/pointer wiring) are tracked via `relate_region_at`
    /// against the global `MetaRegionOwners`, NOT through this predicate.
    pub open spec fn inv_at(self, i: int) -> bool {
        &&& self.list[i].inv()
        &&& self.list[i].in_list == self.list_id
    }

    /// The region slot index keyed by the `i`-th link's meta-slot address.
    pub open spec fn slot_index_at(self, i: int) -> usize {
        frame_to_index(meta_to_frame_spec(self.list[i].paddr))
    }

    /// The typed permission for the `i`-th link, reconstructed from the region:
    /// the outer pointer-perm `regions.slots[idx]` paired with the inner perms
    /// `regions.slot_owners[idx].inner_perms`.
    pub open spec fn meta_perm_of(
        self,
        regions: MetaRegionOwners,
        i: int,
    ) -> vstd_extra::cast_ptr::PointsTo<MetaSlot, Metadata<Link<M>>> {
        let idx = self.slot_index_at(i);
        vstd_extra::cast_ptr::PointsTo::new_spec(
            regions.slots[idx],
            regions.slot_owners[idx].inner_perms,
        )
    }

    /// The per-link invariant expressed over the *region* permission
    /// (`meta_perm_of`) rather than the list's owned `perms[i]`. This is the
    /// `inv_at` analog that connects each list element to its region slot, so
    /// accessors can reason about the link's metadata without bringing the
    /// list's `perms[i]` into scope (which would conflict — two permissions at
    /// the same address).
    #[verifier::opaque]
    pub open spec fn relate_region_at(self, regions: MetaRegionOwners, i: int) -> bool {
        let idx = self.slot_index_at(i);
        let perm = self.meta_perm_of(regions, i);
        &&& regions.slots.contains_key(idx)
        &&& regions.slot_owners.contains_key(idx)
        &&& perm.addr() == self.list[i].paddr
        &&& perm.points_to.addr() == self.list[i].paddr
        &&& perm.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
        &&& perm.wf(&perm.inner_perms)
        &&& perm.addr() % META_SLOT_SIZE == 0
        &&& FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.start + MAX_NR_PAGES
            * META_SLOT_SIZE
        &&& perm.is_init()
        &&& perm.value().metadata.wf(self.list[i])
        &&& i == 0 <==> perm.value().metadata.prev is None
        &&& i == self.list.len() - 1 <==> perm.value().metadata.next is None
        &&& 0 < i ==> {
            &&& perm.value().metadata.prev is Some
            &&& perm.value().metadata.prev.unwrap().addr() == self.meta_perm_of(
                regions,
                i - 1,
            ).addr()
            &&& perm.value().metadata.prev.unwrap().ptr == self.meta_perm_of(
                regions,
                i - 1,
            ).points_to.pptr()
        }
        &&& i < self.list.len() - 1 ==> {
            &&& perm.value().metadata.next is Some
            &&& perm.value().metadata.next.unwrap().addr() == self.meta_perm_of(
                regions,
                i + 1,
            ).addr()
            &&& perm.value().metadata.next.unwrap().ptr == self.meta_perm_of(
                regions,
                i + 1,
            ).points_to.pptr()
        }
        &&& self.list[i].inv()
        &&& self.list[i].in_list == self.list_id
    }

    /// The list-wide region relation: every link satisfies `relate_region_at`,
    /// and distinct list positions map to distinct region slot indices (so a
    /// frame appears at most once — required by the borrow model, where link
    /// edits mutate `regions.slots[slot_index_at(i)]` and must not alias).
    pub open spec fn relate_region(self, regions: MetaRegionOwners) -> bool {
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
        let idxs = Seq::new(self.list.len(), |i: int| self.slot_index_at(i) as int);

        assert(idxs.no_duplicates()) by {
            assert forall|i: int, j: int|
                0 <= i < idxs.len() && 0 <= j < idxs.len() && i != j implies idxs[i] != idxs[j] by {
                let a = self.slot_index_at(i);
                let b = self.slot_index_at(j);
                // `relate_region`'s injectivity gives `a != b`.
            }
        }
        idxs.unique_seq_to_set();

        let bound = set_int_range(0, max_meta_slots());
        assert(idxs.to_set().subset_of(bound)) by {
            assert forall|x: int|
                #![trigger idxs.to_set().contains(x)]
                idxs.to_set().contains(x) implies bound.contains(x) by {
                let i = choose|i: int| 0 <= i < idxs.len() && idxs[i] == x;
                let _ = self.list[i];
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
        assert(max_meta_slots() < usize::MAX) by (compute_only);
    }

    /// Unfolds the opaque `relate_region_at` ONCE and exposes its clauses.
    /// `relate_region_at` is opaque to avoid `meta_perm_of` quantifier
    /// explosion at use sites; this lemma localizes the reveal so callers get
    /// the facts at a single index without re-exploding the SMT context.
    pub proof fn relate_region_at_facts(self, regions: MetaRegionOwners, i: int)
        requires
            self.relate_region_at(regions, i),
        ensures
            ({
                let idx = self.slot_index_at(i);
                let perm = self.meta_perm_of(regions, i);
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners.contains_key(idx)
                &&& perm.addr() == self.list[i].paddr
                &&& perm.points_to.addr() == self.list[i].paddr
                &&& perm.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                &&& perm.wf(&perm.inner_perms)
                &&& perm.addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.start
                    + MAX_NR_PAGES * META_SLOT_SIZE
                &&& perm.is_init()
                &&& perm.value().metadata.wf(self.list[i])
                &&& (i == 0 <==> perm.value().metadata.prev is None)
                &&& (i == self.list.len() - 1 <==> perm.value().metadata.next is None)
                &&& (0 < i ==> {
                    &&& perm.value().metadata.prev is Some
                    &&& perm.value().metadata.prev.unwrap().addr() == self.meta_perm_of(
                        regions,
                        i - 1,
                    ).addr()
                    &&& perm.value().metadata.prev.unwrap().ptr == self.meta_perm_of(
                        regions,
                        i - 1,
                    ).points_to.pptr()
                })
                &&& (i < self.list.len() - 1 ==> {
                    &&& perm.value().metadata.next is Some
                    &&& perm.value().metadata.next.unwrap().addr() == self.meta_perm_of(
                        regions,
                        i + 1,
                    ).addr()
                    &&& perm.value().metadata.next.unwrap().ptr == self.meta_perm_of(
                        regions,
                        i + 1,
                    ).points_to.pptr()
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
                let perm = self.meta_perm_of(regions, i);
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners.contains_key(idx)
                &&& perm.addr() == self.list[i].paddr
                &&& perm.points_to.addr() == self.list[i].paddr
                &&& perm.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                &&& perm.wf(&perm.inner_perms)
                &&& perm.addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= perm.addr() < FRAME_METADATA_RANGE.start
                    + MAX_NR_PAGES * META_SLOT_SIZE
                &&& perm.is_init()
                &&& perm.value().metadata.wf(self.list[i])
                &&& (i == 0 <==> perm.value().metadata.prev is None)
                &&& (i == self.list.len() - 1 <==> perm.value().metadata.next is None)
                &&& (0 < i ==> {
                    &&& perm.value().metadata.prev is Some
                    &&& perm.value().metadata.prev.unwrap().addr() == self.meta_perm_of(
                        regions,
                        i - 1,
                    ).addr()
                    &&& perm.value().metadata.prev.unwrap().ptr == self.meta_perm_of(
                        regions,
                        i - 1,
                    ).points_to.pptr()
                })
                &&& (i < self.list.len() - 1 ==> {
                    &&& perm.value().metadata.next is Some
                    &&& perm.value().metadata.next.unwrap().addr() == self.meta_perm_of(
                        regions,
                        i + 1,
                    ).addr()
                    &&& perm.value().metadata.next.unwrap().ptr == self.meta_perm_of(
                        regions,
                        i + 1,
                    ).points_to.pptr()
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
            if k > 0 {
                let _ = self.list[k - 1];
            }
            if k < llen - 1 {
                let _ = self.list[k + 1];
            }
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
    #[verifier::rlimit(8000)]
    #[verifier::spinoff_prover]
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
            new.list_id == old.list_id,
            forall|p: int|
                #![trigger old.slot_index_at(p)]
                (0 <= p < old.list.len() && p != n) ==> ({
                    let i = old.slot_index_at(p);
                    let fp = vstd_extra::cast_ptr::PointsTo::<
                        MetaSlot,
                        Metadata<Link<M>>,
                    >::new_spec(fr.slots[i], fr.slot_owners[i].inner_perms);
                    &&& fr.slots.contains_key(i)
                    &&& fr.slot_owners.contains_key(i)
                    &&& fp.addr() == old.list[p].paddr
                    &&& fp.points_to.addr() == old.list[p].paddr
                    &&& fp.points_to.pptr() == r0.slots[i].pptr()
                    &&& fp.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                    &&& fp.wf(&fp.inner_perms)
                    &&& fp.addr() % META_SLOT_SIZE == 0
                    &&& FRAME_METADATA_RANGE.start <= fp.addr() < FRAME_METADATA_RANGE.start
                        + MAX_NR_PAGES * META_SLOT_SIZE
                    &&& fp.is_init()
                    &&& (p == n - 1 ==> fp.value().metadata.next == old.meta_perm_of(
                        r0,
                        n,
                    ).value().metadata.next)
                    &&& (p != n - 1 ==> fp.value().metadata.next == old.meta_perm_of(
                        r0,
                        p,
                    ).value().metadata.next)
                    &&& (p == n + 1 ==> fp.value().metadata.prev == old.meta_perm_of(
                        r0,
                        n,
                    ).value().metadata.prev)
                    &&& (p != n + 1 ==> fp.value().metadata.prev == old.meta_perm_of(
                        r0,
                        p,
                    ).value().metadata.prev)
                }),
        ensures
            new.relate_region(fr),
    {
        let nlen = new.list.len() as int;
        assert(nlen == old.list.len() - 1);

        assert forall|k: int| #![trigger new.slot_index_at(k)] 0 <= k < nlen implies {
            let p = if k < n {
                k
            } else {
                k + 1
            };
            &&& new.list[k] == old.list[p]
            &&& new.slot_index_at(k) == old.slot_index_at(p)
        } by {
            assert(new.list[k] == old.list.remove(n)[k]);
        }

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
            assert(pa != pb);
            assert(new.slot_index_at(a) == old.slot_index_at(pa));
            assert(new.slot_index_at(b) == old.slot_index_at(pb));
        }

        assert forall|m: int| #![trigger new.meta_perm_of(fr, m)] 0 <= m < nlen implies {
            let pm = if m < n {
                m
            } else {
                m + 1
            };
            &&& new.meta_perm_of(fr, m).addr() == old.meta_perm_of(r0, pm).addr()
            &&& new.meta_perm_of(fr, m).points_to.pptr() == old.meta_perm_of(
                r0,
                pm,
            ).points_to.pptr()
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
                let _ = old.list[n + 1];
                old.relate_region_at_facts(r0, n + 1);
            }
            new.relate_region_at_from_clauses(fr, k);
        }

        assert(new.list.len() > 0 ==> new.list_id != 0);
        assert(new.relate_region(fr));
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
    #[verifier::rlimit(8000)]
    #[verifier::spinoff_prover]
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
            new.list_id != 0,
            old.list.len() > 0 ==> new.list_id == old.list_id,
            link.in_list == new.list_id,
            forall|p: int|
                #![trigger old.slot_index_at(p)]
                (0 <= p < old.list.len()) ==> old.slot_index_at(p) != new.slot_index_at(n),
            ({
                let ins = new.slot_index_at(n);
                let fpn = vstd_extra::cast_ptr::PointsTo::<MetaSlot, Metadata<Link<M>>>::new_spec(
                    fr.slots[ins],
                    fr.slot_owners[ins].inner_perms,
                );
                &&& fr.slots.contains_key(ins)
                &&& fr.slot_owners.contains_key(ins)
                &&& fpn.addr() == link.paddr
                &&& fpn.points_to.addr() == link.paddr
                &&& fpn.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                &&& fpn.wf(&fpn.inner_perms)
                &&& fpn.addr() % META_SLOT_SIZE == 0
                &&& FRAME_METADATA_RANGE.start <= fpn.addr() < FRAME_METADATA_RANGE.start
                    + MAX_NR_PAGES * META_SLOT_SIZE
                &&& fpn.is_init()
                &&& (n == 0 <==> fpn.value().metadata.prev is None)
                &&& (n == old.list.len() <==> fpn.value().metadata.next is None)
                &&& (n > 0 ==> {
                    &&& fpn.value().metadata.prev is Some
                    &&& fpn.value().metadata.prev.unwrap().addr() == old.list[n - 1].paddr
                    &&& fpn.value().metadata.prev.unwrap().ptr == r0.slots[old.slot_index_at(
                        n - 1,
                    )].pptr()
                })
                &&& (n < old.list.len() ==> {
                    &&& fpn.value().metadata.next is Some
                    &&& fpn.value().metadata.next.unwrap().addr() == old.list[n].paddr
                    &&& fpn.value().metadata.next.unwrap().ptr == r0.slots[old.slot_index_at(
                        n,
                    )].pptr()
                })
            }),
            forall|p: int|
                #![trigger old.slot_index_at(p)]
                (0 <= p < old.list.len()) ==> ({
                    let i = old.slot_index_at(p);
                    let ins = new.slot_index_at(n);
                    let fp = vstd_extra::cast_ptr::PointsTo::<
                        MetaSlot,
                        Metadata<Link<M>>,
                    >::new_spec(fr.slots[i], fr.slot_owners[i].inner_perms);
                    &&& fr.slots.contains_key(i)
                    &&& fr.slot_owners.contains_key(i)
                    &&& fp.addr() == old.list[p].paddr
                    &&& fp.points_to.addr() == old.list[p].paddr
                    &&& fp.points_to.pptr() == r0.slots[i].pptr()
                    &&& fp.inner_perms.ref_count.value() == REF_COUNT_UNIQUE
                    &&& fp.wf(&fp.inner_perms)
                    &&& fp.addr() % META_SLOT_SIZE == 0
                    &&& FRAME_METADATA_RANGE.start <= fp.addr() < FRAME_METADATA_RANGE.start
                        + MAX_NR_PAGES * META_SLOT_SIZE
                    &&& fp.is_init()
                    &&& (p == n - 1 ==> {
                        &&& fp.value().metadata.next is Some
                        &&& fp.value().metadata.next.unwrap().addr() == link.paddr
                        &&& fp.value().metadata.next.unwrap().ptr == fr.slots[ins].pptr()
                    })
                    &&& (p != n - 1 ==> fp.value().metadata.next == old.meta_perm_of(
                        r0,
                        p,
                    ).value().metadata.next)
                    &&& (p == n ==> {
                        &&& fp.value().metadata.prev is Some
                        &&& fp.value().metadata.prev.unwrap().addr() == link.paddr
                        &&& fp.value().metadata.prev.unwrap().ptr == fr.slots[ins].pptr()
                    })
                    &&& (p != n ==> fp.value().metadata.prev == old.meta_perm_of(
                        r0,
                        p,
                    ).value().metadata.prev)
                }),
        ensures
            new.relate_region(fr),
    {
        let nlen = new.list.len() as int;
        assert(nlen == old.list.len() + 1);
        let ins = new.slot_index_at(n);

        assert forall|k: int| #![trigger new.slot_index_at(k)] 0 <= k < nlen implies ({
            &&& (k < n ==> new.list[k] == old.list[k] && new.slot_index_at(k) == old.slot_index_at(
                k,
            ))
            &&& (k == n ==> new.list[k] == link && new.slot_index_at(k) == ins)
            &&& (k > n ==> new.list[k] == old.list[k - 1] && new.slot_index_at(k)
                == old.slot_index_at(k - 1))
        }) by {
            assert(new.list[k] == old.list.insert(n, link)[k]);
        }

        assert forall|a: int, b: int|
            #![trigger new.slot_index_at(a), new.slot_index_at(b)]
            0 <= a < nlen && 0 <= b < nlen && a != b implies new.slot_index_at(a)
            != new.slot_index_at(b) by {
            let _ = new.slot_index_at(a);
            let _ = new.slot_index_at(b);
            if a != n {
                let pa = if a < n {
                    a
                } else {
                    a - 1
                };
                let _ = old.slot_index_at(pa);
            }
            if b != n {
                let pb = if b < n {
                    b
                } else {
                    b - 1
                };
                let _ = old.slot_index_at(pb);
            }
        }

        assert forall|m: int| #![trigger new.meta_perm_of(fr, m)] 0 <= m < nlen implies ({
            &&& (m < n ==> new.meta_perm_of(fr, m).addr() == old.meta_perm_of(r0, m).addr()
                && new.meta_perm_of(fr, m).points_to.pptr() == old.meta_perm_of(
                r0,
                m,
            ).points_to.pptr())
            &&& (m > n ==> new.meta_perm_of(fr, m).addr() == old.meta_perm_of(r0, m - 1).addr()
                && new.meta_perm_of(fr, m).points_to.pptr() == old.meta_perm_of(
                r0,
                m - 1,
            ).points_to.pptr())
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
            let _ = old.slot_index_at(n - 1);
            let _ = old.slot_index_at(n);
            new.relate_region_at_from_clauses(fr, k);
        }

        // `new` has `old.len + 1 ≥ 1 > 0` elements and a non-zero id by hypothesis.
        assert(new.list.len() > 0 ==> new.list_id != 0);
        assert(new.relate_region(fr));
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
            Self::view_helper(owners.insert(i, v)) == Self::view_helper(owners).insert(
                i,
                v.view(),
            ),
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
        &&& owner.list.len() > 0 ==> self.front is Some && self.front.unwrap().addr()
            == owner.list[0].paddr && self.back is Some && self.back.unwrap().addr()
            == owner.list[owner.list.len() - 1].paddr
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

    /// Structural well-formedness: `current` matches the link at `index`'s
    /// address. Pointer-permission facts (pptr/ptr equality) are stated in
    /// `wf_region` over `meta_perm_of(regions, _)`.
    open spec fn wf(self, owner: Self::Owner) -> bool {
        &&& 0 <= owner.index < owner.length() ==> self.current.is_some()
            && self.current.unwrap().addr() == owner.list_own.list[owner.index].paddr
        &&& owner.index == owner.list_own.list.len() ==> self.current.is_none()
        &&& (*self.list).wf(owner.list_own)
    }
}

impl<M: AnyFrameMeta + Repr<MetaSlotSmall>> LinkedList<M> {
    /// Region-based analog of [`LinkedList::wf`]: the front/back pointer facts
    /// are stated over `owner.meta_perm_of(regions, _)` instead of the list's
    /// owned `perms`. Used by accessors that source link permissions from
    /// `regions` and so must not bring `perms[i]` into scope.
    pub open spec fn wf_region(self, owner: LinkedListOwner<M>, regions: MetaRegionOwners) -> bool {
        &&& self.front is None <==> owner.list.len() == 0
        &&& self.back is None <==> owner.list.len() == 0
        &&& owner.list.len() > 0 ==> self.front is Some && self.front.unwrap().addr()
            == owner.list[0].paddr && owner.meta_perm_of(regions, 0).pptr().addr()
            == self.front.unwrap().addr() && self.front.unwrap().ptr == owner.meta_perm_of(
            regions,
            0,
        ).points_to.pptr() && self.back is Some && self.back.unwrap().addr()
            == owner.list[owner.list.len() - 1].paddr && owner.meta_perm_of(
            regions,
            owner.list.len() - 1,
        ).pptr().addr() == self.back.unwrap().addr() && self.back.unwrap().ptr
            == owner.meta_perm_of(regions, owner.list.len() - 1).points_to.pptr()
        &&& self.size == owner.list.len()
        &&& self.list_id == owner.list_id
    }
}

impl<'a, M: AnyFrameMeta + Repr<MetaSlotSmall>> CursorMut<'a, M> {
    /// Region-based analog of [`CursorMut::wf`]: the current-link pointer facts
    /// are stated over `owner.list_own.meta_perm_of(regions, index)`.
    pub open spec fn wf_region(self, owner: CursorOwner<M>, regions: MetaRegionOwners) -> bool {
        &&& 0 <= owner.index < owner.length() ==> self.current.is_some()
            && self.current.unwrap().addr() == owner.list_own.list[owner.index].paddr
            && owner.list_own.meta_perm_of(regions, owner.index).pptr().addr()
            == self.current.unwrap().addr() && self.current.unwrap().ptr
            == owner.list_own.meta_perm_of(regions, owner.index).points_to.pptr()
        &&& owner.index == owner.list_own.list.len() ==> self.current.is_none()
        &&& (*self.list).wf_region(owner.list_own, regions)
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

    /// Region-based analog of [`CursorOwner::inv`]: replaces `list_own.inv()`
    /// (over the owned `perms`) with `list_own.relate_region(regions)` (over
    /// the region permissions).
    pub open spec fn inv_region(self, regions: MetaRegionOwners) -> bool {
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

    /// Tracked update to the cursor's owner state when a new link is inserted
    /// before the current position. The inserted `link`'s `paddr` is unchanged
    /// and its `in_list` is stamped with `list_id` — the (non-zero) id the
    /// concrete `lazy_get_id` resolved. The cursor's list gains `link` at
    /// `old.index`, adopts `list_id` (which equals the old id when that was
    /// already non-zero), and `index` advances by one. In the borrow model, the
    /// link's tracked permission remains parked in `MetaRegionOwners.slots`;
    /// this axiom doesn't need to take or carry a perm.
    pub axiom fn list_insert(tracked cursor: &mut Self, tracked link: &mut LinkOwner, list_id: u64)
        requires
            list_id != 0,
            old(cursor).list_own.list_id != 0 ==> list_id == old(cursor).list_own.list_id,
        ensures
            final(link).paddr == old(link).paddr,
            final(link).in_list == list_id,
            final(cursor).list_own.list == old(cursor).list_own.list.insert(
                old(cursor).index,
                *final(link),
            ),
            final(cursor).list_own.list_id == list_id,
            final(cursor).index == old(cursor).index + 1,
    ;

    pub open spec fn front_owner(list_own: LinkedListOwner<M>) -> Self {
        CursorOwner::<M> { list_own: list_own, index: 0 }
    }

    pub open spec fn cursor_mut_at_owner(list_own: LinkedListOwner<M>, index: int) -> Self {
        CursorOwner::<M> { list_own: list_own, index: index }
    }

    pub axiom fn tracked_cursor_mut_at_owner(
        list_own: LinkedListOwner<M>,
        index: int,
    ) -> (tracked res: Self)
        ensures
            res == Self::cursor_mut_at_owner(list_own, index),
    ;

    pub axiom fn tracked_front_owner(list_own: LinkedListOwner<M>) -> (tracked res: Self)
        ensures
            res == Self::front_owner(list_own),
    ;

    pub open spec fn back_owner(list_own: LinkedListOwner<M>) -> Self {
        CursorOwner::<M> {
            list_own: list_own,
            index: if list_own.list.len() > 0 {
                list_own.list.len() as int - 1
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
                list_own.list.len() as int - 1
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
        &&& self.meta_perm_of(regions).value().metadata.prev is None
        &&& self.meta_perm_of(regions).value().metadata.next is None
        &&& self.meta_own.paddr == self.meta_perm_of(regions).addr()
    }
}

pub struct MetadataAsLink<M: AnyFrameMeta + Repr<MetaSlotSmall>> {
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
    fn from_borrowed<'a>(
        r: &'a MetaSlot,
        Tracked(perm): Tracked<&'a MetadataInnerPerms>,
    ) -> &'a Self {
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
    pub fn cast_to_metadata(ptr: ReprPtr<MetaSlot, Self>) -> (res: ReprPtr<
        MetaSlot,
        Metadata<Link<M>>,
    >)
        ensures
            res.addr() == ptr.addr(),
            res.ptr == ptr.ptr,
    {
        ReprPtr { ptr: ptr.ptr, _T: PhantomData }
    }

    pub fn cast_from_metadata(ptr: ReprPtr<MetaSlot, Metadata<Link<M>>>) -> (res: ReprPtr<
        MetaSlot,
        Self,
    >)
        ensures
            res.addr() == ptr.addr(),
            res.ptr == ptr.ptr,
    {
        ReprPtr { ptr: ptr.ptr, _T: PhantomData }
    }
}

} // verus!
