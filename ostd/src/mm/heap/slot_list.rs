// SPDX-License-Identifier: MPL-2.0
//! Implementation of the free heap slot list.
use vstd::{
    layout::{align_of, size_of},
    prelude::*,
    raw_ptr::{self, IsExposed, PointsTo, PointsToRaw, group_raw_ptr_axioms},
};
use vstd_extra::ownership::Inv;

use crate::mm::{
    heap::SlotInfo,
    kspace::{LINEAR_MAPPING_BASE_VADDR, VMALLOC_BASE_VADDR},
};

use core::ptr::NonNull;

use super::HeapSlot;

verus! {

tracked struct SlotNode {
    word: PointsTo<usize>,
    rest: PointsToRaw,
    next_exposed: IsExposed,
}

/// A singly-linked list of [`HeapSlot`]s from [`super::Slab`]s.
///
/// The slots inside this list will have a size of `SLOT_SIZE`. They can come
/// from different slabs.
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct SlabSlotList<const SLOT_SIZE: usize> {
    /// The head of the list.
    head: Option<NonNull<u8>>,
    #[cfg(verus_keep_ghost_body)]
    ghost_slots: Ghost<Seq<*mut u8>>,
    #[cfg(verus_keep_ghost_body)]
    tracked_nodes: Tracked<Map<int, SlotNode>>,
}

// SAFETY: Any access or modification (i.e., push and pop operations) to the
// data pointed to by `head` requires a `&mut SlabSlotList`. Therefore, at any
// given time, only one task can access the inner `head`. Additionally, a
// `HeapSlot` will not be allocated again as long as it remains in the list.
#[verifier::external]
unsafe impl<const SLOT_SIZE: usize> Sync for SlabSlotList<SLOT_SIZE> {

}

#[verifier::external]
unsafe impl<const SLOT_SIZE: usize> Send for SlabSlotList<SLOT_SIZE> {

}

} // verus!
#[verus_verify]
impl<const SLOT_SIZE: usize> Default for SlabSlotList<SLOT_SIZE> {
    #[verus_spec(res =>
        ensures
            res.inv(),
            res.slots() == Seq::<*mut u8>::empty(),
    )]
    fn default() -> Self {
        Self::new()
    }
}

verus! {

impl<const SLOT_SIZE: usize> Inv for SlabSlotList<SLOT_SIZE> {
    closed spec fn inv(self) -> bool {
        let slots = self.slots();
        &&& self.head matches Some(h) ==> slots.len() > 0 && h.as_ptr() == slots.last()
        &&& self.head is None <==> slots.len() == 0
        &&& self.tracked_nodes@.dom() == Set::range(0, slots.len() as int)
        &&& forall|i: int| 0 <= i < slots.len() ==> #[trigger] self.node_inv(i)
        &&& slots.map_values(|p: *mut u8| p.addr()).no_duplicates()
    }
}

impl<const SLOT_SIZE: usize> SlabSlotList<SLOT_SIZE> {
    /// Slots in insertion order; the last slot is the head returned by `pop`.
    pub closed spec fn slots(self) -> Seq<*mut u8> {
        self.ghost_slots@
    }

    /// The permissions and initialized links of every surviving node are unchanged.
    pub closed spec fn preserves_nodes(self, previous: Self) -> bool {
        forall|i: int|
            0 <= i < self.slots().len() && i < previous.slots().len()
                ==> #[trigger] self.tracked_nodes@[i] == previous.tracked_nodes@[i]
    }

    closed spec fn node_inv(self, i: int) -> bool {
        let slots = self.slots();
        let node = self.tracked_nodes@[i];
        let ptr = slots[i];
        let next = if i == 0 {
            core::ptr::null_mut::<u8>()
        } else {
            slots[i - 1]
        };
        &&& SLOT_SIZE >= size_of::<usize>()
        &&& ptr.addr() != 0
        &&& LINEAR_MAPPING_BASE_VADDR <= ptr.addr()
        &&& ptr.addr() + SLOT_SIZE <= VMALLOC_BASE_VADDR
        &&& node.word.ptr() == ptr as *mut usize
        &&& node.word.is_init()
        &&& node.word.value() == next.addr()
        &&& node.rest.is_range(ptr.addr() + size_of::<usize>(), SLOT_SIZE - size_of::<usize>())
        &&& node.rest.provenance() == ptr@.provenance
        &&& node.next_exposed.provenance() == next@.provenance
    }
}

} // verus!
#[verus_verify]
impl<const SLOT_SIZE: usize> SlabSlotList<SLOT_SIZE> {
    /// Creates a new empty list.
    #[verus_spec(res =>
        ensures
            res.inv(),
            res.slots() == Seq::<*mut u8>::empty(),
    )]
    pub const fn new() -> Self {
        proof! {
            assert(Set::<int>::range(0, 0) == Set::<int>::empty());
        }
        Self {
            head: None,
            #[cfg(verus_keep_ghost_body)]
            ghost_slots: verus_exec_expr!(Ghost(Seq::empty())),
            #[cfg(verus_keep_ghost_body)]
            tracked_nodes: verus_exec_expr!(Tracked(Map::tracked_empty())),
        }
    }

    /// Pushes a slot to the front of the list.
    ///
    /// # Panics
    ///
    /// Panics if
    ///  - the slot does not come from a slab
    ///    (i.e., `!matches(slot.info(), SlotInfo::SlabSlot(_))`);
    ///  - the size of the slot does not match `SLOT_SIZE`.
    #[verus_spec(
        requires
            old(self).inv(),
            slot.inv(),
            cfg!(feature = "allow_panic") ==> slot.slot_info() is SlabSlot,
            SLOT_SIZE >= size_of::<usize>(),
            slot.slot_info() is SlabSlot ==> {
                &&& slot.slot_info().size_spec() == SLOT_SIZE
                &&& slot.ptr().addr() as int % align_of::<usize>() as int == 0
            },
        ensures
            final(self).inv(),
            final(self).preserves_nodes(*old(self)),
            final(self).slots() == if slot.slot_info() is SlabSlot {
                old(self).slots().push(slot.ptr())
            } else {
                old(self).slots()
            },
    )]
    pub fn push(&mut self, slot: HeapSlot) {
        proof_decl! {
            broadcast use group_raw_ptr_axioms;

            let ghost original = *self;
            let ghost before = self.slots();
        }
        let slot_ptr = slot.as_ptr();
        let super::SlotInfo::SlabSlot(slot_size) = slot.info() else {
            #[cfg(feature = "allow_panic")]
            panic!("The slot does not come from a slab");
            #[cfg(not(feature = "allow_panic"))]
            return;
        };

        #[cfg(feature = "allow_panic")]
        assert_eq!(slot_size, SLOT_SIZE);
        // Verus cannot translate inline const blocks; the same bound is proved above.
        #[cfg(not(verus_keep_ghost))]
        const {
            assert!(SLOT_SIZE >= core::mem::size_of::<usize>())
        };
        let mem = slot.into_memory();
        proof_decl! {
            let tracked (word_mem, rest) = mem.get().split(
                Set::range(slot_ptr.addr() as int, slot_ptr.addr() + size_of::<usize>()),
            );
            let tracked mut word = word_mem.into_typed::<usize>(slot_ptr.addr());
        }
        proof! {
            word.is_nonnull();
            // Distinct header permissions establish freshness without a caller-supplied address axiom.
            proof fn tracked_distinct(
                tracked word: &mut PointsTo<usize>,
                tracked nodes: &Map<int, SlotNode>,
                n: nat,
            )
                requires
                    forall|i: int| 0 <= i < n ==> nodes.contains_key(i),
                ensures
                    *final(word) == *old(word),
                    forall|i: int|
                        0 <= i < n ==> final(word).ptr().addr()
                            != #[trigger] nodes[i].word.ptr().addr(),
                decreases n,
            {
                if n > 0 {
                    word.is_disjoint(&nodes.tracked_borrow(n - 1).word);
                    tracked_distinct(word, nodes, (n - 1) as nat);
                }
            }
            tracked_distinct(&mut word, self.tracked_nodes.borrow(), before.len());
        }

        let original_head = self.head;

        debug_assert!(!slot_ptr.is_null());
        // SAFETY: A pointer to a slot must not be NULL;
        self.head = Some(unsafe { NonNull::new_unchecked(slot_ptr) });
        // Write the original head to the slot.
        // SAFETY: A heap slot must be free so the pointer to the slot can be
        // written to. The slot size is at least the size of a pointer.
        /* Origin Rust: slot_ptr.cast::<usize>().write(
         *     original_head.map_or(0, |h| h.as_ptr() as usize));
         * The permission-aware write has the same address and usize payload;
         * expose the next pointer's provenance for pop's integer round trip.
         */
        proof_decl! {
            let tracked mut next_exposed = IsExposed::null();
        }
        let link = match original_head {
            Some(h) => {
                let p = h.as_ptr();
                let exposure = raw_ptr::expose_provenance(p);
                proof! {
                    next_exposed = exposure.get();
                }
                p as usize
            }
            None => 0,
        };
        verus_exec_expr! {
            raw_ptr::ptr_mut_write(slot_ptr.cast::<usize>(), Tracked(&mut word), link)
        };
        proof! {
            self.tracked_nodes.borrow_mut().tracked_insert(
                before.len() as int,
                SlotNode { word, rest, next_exposed },
            );
            self.ghost_slots = Ghost(before.push(slot_ptr));
            assert(self.tracked_nodes@.dom() == Set::range(0, self.slots().len() as int));
            assert forall|i: int| 0 <= i < self.slots().len() implies #[trigger] self.node_inv(
                i,
            ) by {
                if i < before.len() {
                    assert(original.node_inv(i));
                }
            }
            assert forall|i: int| 0 <= i < before.len() implies #[trigger] before[i].addr()
                != slot_ptr.addr() by {
                assert(original.node_inv(i));
            }
            assert(self.slots().map_values(|p: *mut u8| p.addr()) == before.map_values(
                |p: *mut u8| p.addr(),
            ).push(slot_ptr.addr()));
        }
    }

    /// Pops a slot from the front of the list.
    ///
    /// It returns `None` if the list is empty.
    #[verus_spec(res =>
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            final(self).preserves_nodes(*old(self)),
            res is None <==> old(self).slots().len() == 0,
            res matches Some(slot) ==> {
                &&& slot.inv()
                &&& slot.ptr() == old(self).slots().last()
                &&& slot.slot_info() == SlotInfo::SlabSlot(SLOT_SIZE)
                &&& SLOT_SIZE >= size_of::<usize>()
                &&& slot.ptr().addr() as int % align_of::<usize>() as int == 0
                &&& final(self).slots() == old(self).slots().drop_last()
            },
            res is None ==> final(self).slots() == old(self).slots(),
    )]
    pub fn pop(&mut self) -> Option<HeapSlot> {
        proof_decl! {
            broadcast use group_raw_ptr_axioms;

            let ghost original = *self;
            let ghost before = self.slots();
        }
        let original_head = self.head?;
        proof_decl! {
            let tracked mut node = self.tracked_nodes.borrow_mut().tracked_remove(before.len() - 1);
        }
        proof! {
            assert(original.node_inv(before.len() - 1));
            node.word.is_aligned();
            if before.len() > 1 {
                assert(original.node_inv(before.len() - 2));
            }
        }

        // SAFETY: The head is a valid pointer to a free slot.
        // The slot contains a pointer to the next slot.
        /* Origin Rust: original_head.as_ptr().cast::<usize>().read() as *mut u8;
         * Read with the exclusive initialized-word permission and restore the
         * provenance exposed by push, retaining the usize link representation.
         */
        let link = verus_exec_expr! {
            raw_ptr::ptr_mut_read(
                original_head.as_ptr().cast::<usize>(),
                Tracked(&mut node.word),
            )
        };
        let next = verus_exec_expr! {
            raw_ptr::with_exposed_provenance::<u8>(link, Tracked(node.next_exposed))
        };

        self.head = if next.is_null() {
            None
        } else {
            // SAFETY: We already verified that the next slot is not NULL.
            Some(unsafe { NonNull::new_unchecked(next) })
        };

        proof_decl! {
            let tracked mem = node.word.into_raw().join(node.rest);
        }
        proof! {
            self.ghost_slots = Ghost(before.drop_last());
            assert(self.slots().map_values(|p: *mut u8| p.addr()) == before.map_values(
                |p: *mut u8| p.addr(),
            ).drop_last());
            assert(self.tracked_nodes@.dom() == Set::range(0, self.slots().len() as int));
            assert forall|i: int| 0 <= i < self.slots().len() implies #[trigger] self.node_inv(
                i,
            ) by {
                assert(original.node_inv(i));
            }
        }
        Some(unsafe {
            verus_exec_expr! {
                HeapSlot::new(original_head, super::SlotInfo::SlabSlot(SLOT_SIZE), Tracked(mem))
            }
        })
    }
}
