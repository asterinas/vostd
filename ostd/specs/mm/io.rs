// SPDX-License-Identifier: MPL-2.0
//! Specification and proof content for [`crate::mm::io`].
//!
//! Holds the tracked owner/view types (`VmIoOwner`, `VmIoMemView`), the
//! trust-boundary axioms that bridge native Rust slices to the tracked
//! memory model, and the `wf`/`inv` impls relating exec reader/writer
//! handles to their ghost owners.
use core::ops::Range;
use vstd::pervasive::{arbitrary, proof_from_false};
use vstd::prelude::*;
use vstd_extra::ownership::Inv;

use crate::mm::io::{Infallible, VmReader, VmWriter};
use crate::mm::kspace::{KERNEL_BASE_VADDR, KERNEL_END_VADDR};
use crate::specs::mm::virt_mem::MemView;

verus! {

// =============================================================================
// Trust-boundary axioms
// =============================================================================

/// AXIOM: every `&[u8]` reaching ostd refers to kernel-space memory.
///
/// `ostd` is only ever called from kernel code, so any "native" Rust slice it
/// receives points into kernel-managed memory. The natural trust boundary is
/// here, at the conversion from a native slice to a tracked [`VirtPtr`] / owner;
/// downstream proofs discharge [`VmWriter::from_kernel_space`]'s kernel-VA
/// preconditions via this fact.
///
/// [`VirtPtr`]: crate::specs::mm::virt_mem::VirtPtr
pub axiom fn axiom_slice_in_kernel(slice: &[u8])
    ensures
        ::vstd_extra::external::slice::as_ptr_spec(slice) as usize
            >= KERNEL_BASE_VADDR,
        ::vstd_extra::external::slice::as_ptr_spec(slice) as usize
            + slice.len() <= KERNEL_END_VADDR,
;

/// AXIOM: a fresh `MemView` covering a kernel-VA range exists.
///
/// The kernel guarantees that every byte in `[KERNEL_BASE_VADDR, KERNEL_END_VADDR)`
/// is backed by a valid mapping; this axiom packages that fact as a tracked
/// `MemView` value, suitable for embedding inside a [`VmIoOwner`]. The `Init`
/// part of the returned view (used by [`VmIoOwner::read_view_initialized`]) is
/// claimed unconditionally — `&[u8]` / `&mut [u8]` borrows in safe Rust point
/// to initialized memory, so this is the natural companion to
/// [`axiom_slice_in_kernel`].
pub axiom fn axiom_kernel_mem_view(range: Range<usize>) -> (tracked mv: MemView)
    ensures
        mv.mappings.finite(),
        mv.mappings_are_disjoint(),
        forall|va: usize|
            #![trigger mv.addr_transl(va)]
            range.start <= va < range.end ==> {
                &&& mv.addr_transl(va) is Some
                &&& mv.memory.contains_key(mv.addr_transl(va).unwrap().0)
                &&& mv.memory[mv.addr_transl(va).unwrap().0].contents[mv.addr_transl(
                    va,
                ).unwrap().1 as int] is Init
            },
;

// =============================================================================
// Tracked ownership types
// =============================================================================

/// The memory view used for VM I/O operations.
///
/// The readers can think of this as a wrapped permission tokens for operating with a certain
/// memory view (see [`MemView`]) "owned" by the [`VmIoOwner`] that they are created from, which
/// are used for allowing callers to use [`VmReader`] and [`VmWriter`] to perform VM I/O operations.
///
/// For writers the memory permission must be exclusive so this enum contains an owned [`MemView`]
/// for the write view; for readers the memory permission can be shared so this enum contains a
/// reference to a [`MemView`] for the read view (which can be disabled optionally in [`VmSpaceOwner`]).
///
/// [`VmSpaceOwner`]: crate::mm::vm_space::VmSpaceOwner
pub tracked enum VmIoMemView {
    /// An owned memory for writing.
    WriteView(MemView),
    /// An owned snapshot of memory for reading.
    ReadView(MemView),
}

/// The owner of a VM I/O operation, which tracks the memory range and the memory view for the
/// operation.
///
/// Basically the caller should be only interested in this struct when using [`VmReader`] and
/// [`VmWriter`] to perform VM I/O operations, since the safety of these operations depends on the
/// validity of the memory range and memory view tracked by this struct.
pub tracked struct VmIoOwner {
    /// The unique identifier of this owner.
    pub id: Ghost<nat>,
    /// The virtual address range owned by this owner.
    pub range: Ghost<Range<usize>>,
    /// Whether this reader is fallible.
    pub is_fallible: bool,
    /// Whether this owner is for kernel space.
    pub is_kernel: bool,
    /// The mem view associated with this owner.
    pub mem_view: Option<VmIoMemView>,
}

impl VmIoOwner {
    /// Structural well-formedness: the range is ordered.
    /// Always holds after construction.
    pub open spec fn inv_wf(self) -> bool {
        self.range@.start <= self.range@.end
    }
}

impl Inv for VmIoOwner {
    /// Full invariant: well-formed AND memory view (if present) covers the range.
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& match self.mem_view {
            Some(VmIoMemView::WriteView(mv)) => {
                &&& mv.mappings.finite()
                &&& mv.mappings_are_disjoint()
                &&& forall|va: usize|
                    self.range@.start <= va < self.range@.end ==> {
                        &&& #[trigger] mv.addr_transl(va) is Some
                    }
            },
            Some(VmIoMemView::ReadView(mv)) => {
                &&& mv.mappings.finite()
                &&& mv.mappings_are_disjoint()
                &&& forall|va: usize|
                    self.range@.start <= va < self.range@.end ==> {
                        &&& #[trigger] mv.addr_transl(va) is Some
                    }
            },
            None => true,
        }
    }
}

impl VmIoOwner {
    /// Whether this owner carries a read memory view.
    #[verifier::inline]
    pub open spec fn has_read_view(self) -> bool {
        self.mem_view matches Some(VmIoMemView::ReadView(_))
    }

    /// Whether this owner carries a write memory view.
    #[verifier::inline]
    pub open spec fn has_write_view(self) -> bool {
        self.mem_view matches Some(VmIoMemView::WriteView(_))
    }

    /// Whether this owner is ready to serve as the readable side of a copy.
    #[verifier::inline]
    pub open spec fn can_read(self) -> bool {
        self.has_read_view()
    }

    /// Whether this owner is ready to serve as the writable side of a copy.
    #[verifier::inline]
    pub open spec fn can_write(self) -> bool {
        self.has_write_view()
    }

    /// Whether the read view initializes the entire owner range.
    #[verifier::inline]
    pub open spec fn read_view_initialized(self) -> bool {
        match self.mem_view {
            Some(VmIoMemView::ReadView(mem_src)) => {
                forall|i: usize|
                    #![trigger mem_src.addr_transl(i)]
                    self.range@.start <= i < self.range@.end ==> {
                        &&& mem_src.addr_transl(i) is Some
                        &&& mem_src.memory.contains_key(mem_src.addr_transl(i).unwrap().0)
                        &&& mem_src.memory[mem_src.addr_transl(
                            i,
                        ).unwrap().0].contents[mem_src.addr_transl(i).unwrap().1 as int] is Init
                    }
            },
            _ => false,
        }
    }

    /// Checks whether this owner overlaps with another owner.
    #[verifier::inline]
    pub open spec fn overlaps(self, other: VmIoOwner) -> bool {
        !self.disjoint(other)
    }

    #[verifier::inline]
    pub open spec fn overlaps_with_range(self, range: Range<usize>) -> bool {
        &&& self.range@.start <= range.end
        &&& range.start <= self.range@.end
    }

    /// Checks whether this owner is disjoint with another owner.
    #[verifier::inline]
    pub open spec fn disjoint(self, other: VmIoOwner) -> bool {
        &&& !self.overlaps_with_range(other.range@)
        &&& match (self.mem_view, other.mem_view) {
            (Some(lhs), Some(rhs)) => match (lhs, rhs) {
                (VmIoMemView::WriteView(lmv), VmIoMemView::WriteView(rmv)) => {
                    lmv.mappings.disjoint(rmv.mappings)
                },
                (VmIoMemView::WriteView(lmv), VmIoMemView::ReadView(rmv)) => {
                    lmv.mappings.disjoint(rmv.mappings)
                },
                (VmIoMemView::ReadView(lmv), VmIoMemView::WriteView(rmv)) => {
                    lmv.mappings.disjoint(rmv.mappings)
                },
                (VmIoMemView::ReadView(lmv), VmIoMemView::ReadView(rmv)) => {
                    lmv.mappings.disjoint(rmv.mappings)
                },
            },
            _ => true,
        }
    }

    #[verifier::inline]
    pub open spec fn params_eq(self, other: VmIoOwner) -> bool {
        &&& self.range@ == other.range@
        &&& self.is_fallible == other.is_fallible
    }

    /// Changes the fallibility of this owner.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The new fallibility must differ from the current one.
    /// ## Postconditions
    /// - The updated owner still satisfies its invariant.
    /// - The `is_fallible` field is updated to `fallible`.
    pub proof fn change_fallible(tracked &mut self, tracked fallible: bool)
        requires
            old(self).inv(),
            old(self).is_fallible != fallible,
        ensures
            final(self).inv(),
            final(self).is_fallible == fallible,
    {
        self.is_fallible = fallible;
    }

    /// Advances the cursor of the reader/writer by the given number of bytes.
    ///
    /// Note this will return the advanced `VmIoMemView` as the previous permission
    /// is no longer needed and must be discarded then.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The owner must carry a memory view.
    /// - `nbytes` must not exceed the remaining length of the owned range.
    /// ## Postconditions
    /// - The updated owner still satisfies its invariant.
    /// - The start of the owned range is advanced by `nbytes`.
    /// - The end of the owned range and the other owner parameters are preserved.
    /// - The returned [`VmIoMemView`] is the portion advanced past.
    pub proof fn advance(tracked &mut self, nbytes: usize) -> (tracked res: VmIoMemView)
        requires
            old(self).inv(),
            old(self).mem_view is Some,
            nbytes <= old(self).range@.end - old(self).range@.start,
        ensures
            final(self).inv(),
            final(self).range@.start == old(self).range@.start + nbytes,
            final(self).range@.end == old(self).range@.end,
            final(self).is_fallible == old(self).is_fallible,
            final(self).id == old(self).id,
            final(self).is_kernel == old(self).is_kernel,
            old(self).mem_view matches Some(VmIoMemView::ReadView(_)) ==> final(self).mem_view matches Some(VmIoMemView::ReadView(_)),
            old(self).mem_view matches Some(VmIoMemView::WriteView(_)) ==> final(self).mem_view matches Some(VmIoMemView::WriteView(_)),
            old(self).read_view_initialized() ==> final(self).read_view_initialized(),
    {
        let ghost old_start = self.range@.start;
        let ghost old_end = self.range@.end;
        let ghost old_view_g = self.mem_view;
        let ghost split_end = old_start + nbytes;

        let tracked old_view = self.mem_view.tracked_take();
        let tracked res = match old_view {
            VmIoMemView::WriteView(view) => {
                let ghost view_g = view;
                let tracked (left, right) = view.split(old_start, nbytes);
                MemView::lemma_split_preserves_transl(view_g, old_start, nbytes, left, right);
                assert(right.mappings.finite());
                assert(right.mappings_are_disjoint()) by {
                    assert(right.mappings <= view_g.mappings);
                };
                assert forall|va: usize| split_end <= va < old_end implies
                    #[trigger] right.addr_transl(va) is Some by {
                    assert(view_g.addr_transl(va) is Some);
                    assert(view_g.addr_transl(va) == right.addr_transl(va));
                };
                self.mem_view = Some(VmIoMemView::WriteView(right));
                VmIoMemView::WriteView(left)
            },
            VmIoMemView::ReadView(view) => {
                let ghost view_g = view;
                let tracked (left, right) = view.split(old_start, nbytes);
                MemView::lemma_split_preserves_transl(view_g, old_start, nbytes, left, right);
                assert(right.mappings.finite());
                assert(right.mappings_are_disjoint()) by {
                    assert(right.mappings <= view_g.mappings);
                };
                assert forall|va: usize| split_end <= va < old_end implies
                    #[trigger] right.addr_transl(va) is Some by {
                    assert(view_g.addr_transl(va) is Some);
                    assert(view_g.addr_transl(va) == right.addr_transl(va));
                };
                // If the old view was initialized, the right half stays initialized on its range.
                if old_view_g matches Some(VmIoMemView::ReadView(mv0))
                    && (forall|i: usize|
                        #![trigger mv0.addr_transl(i)]
                        old_start <= i < old_end ==> {
                            &&& mv0.addr_transl(i) is Some
                            &&& mv0.memory.contains_key(mv0.addr_transl(i).unwrap().0)
                            &&& mv0.memory[mv0.addr_transl(i).unwrap().0].contents
                                [mv0.addr_transl(i).unwrap().1 as int] is Init
                        })
                {
                    assert forall|i: usize|
                        #![trigger right.addr_transl(i)]
                        split_end <= i < old_end implies {
                            &&& right.addr_transl(i) is Some
                            &&& right.memory.contains_key(right.addr_transl(i).unwrap().0)
                            &&& right.memory[right.addr_transl(i).unwrap().0].contents
                                [right.addr_transl(i).unwrap().1 as int] is Init
                        } by {
                        assert(view_g.addr_transl(i) == right.addr_transl(i));
                        let pa = right.addr_transl(i).unwrap().0;
                        assert(view_g.memory.contains_key(pa));
                        assert(view_g.is_mapped(i, pa));
                        assert(i >= split_end);
                        assert(right.memory.dom().contains(pa));
                        assert(right.memory[pa] == view_g.memory[pa]);
                    };
                }
                self.mem_view = Some(VmIoMemView::ReadView(right));
                VmIoMemView::ReadView(left)
            },
        };
        self.range = Ghost(Range { start: split_end as usize, end: old_end });
        res
    }

    /// Splits this owner at `nbytes`, returning the front portion as a new owner and shrinking
    /// `self` to cover the back portion.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The owner must carry a memory view.
    /// - `nbytes` must not exceed the remaining length of the owned range.
    /// ## Postconditions
    /// - Both the returned front owner and the updated `self` satisfy their invariants and
    ///   carry the same kind of memory view as the original.
    /// - The front owner covers `[old.start, old.start + nbytes)`.
    /// - `self`'s range becomes `[old.start + nbytes, old.end)`.
    /// - `is_fallible`, `is_kernel` are preserved on both sides.
    /// - If the original was an initialized read view, both sides remain initialized.
    pub proof fn split(tracked &mut self, nbytes: usize) -> (tracked r: VmIoOwner)
        requires
            old(self).inv(),
            old(self).mem_view is Some,
            nbytes <= old(self).range@.end - old(self).range@.start,
        ensures
            r.inv(),
            r.range@.start == old(self).range@.start,
            r.range@.end == old(self).range@.start + nbytes,
            r.is_fallible == old(self).is_fallible,
            r.is_kernel == old(self).is_kernel,
            r.mem_view is Some,
            final(self).inv(),
            final(self).range@.start == old(self).range@.start + nbytes,
            final(self).range@.end == old(self).range@.end,
            final(self).is_fallible == old(self).is_fallible,
            final(self).id == old(self).id,
            final(self).is_kernel == old(self).is_kernel,
            final(self).mem_view is Some,
            old(self).mem_view matches Some(VmIoMemView::ReadView(_)) ==> {
                &&& r.mem_view matches Some(VmIoMemView::ReadView(_))
                &&& final(self).mem_view matches Some(VmIoMemView::ReadView(_))
            },
            old(self).mem_view matches Some(VmIoMemView::WriteView(_)) ==> {
                &&& r.mem_view matches Some(VmIoMemView::WriteView(_))
                &&& final(self).mem_view matches Some(VmIoMemView::WriteView(_))
            },
            old(self).read_view_initialized() ==> {
                &&& r.read_view_initialized()
                &&& final(self).read_view_initialized()
            },
    {
        let ghost old_start = self.range@.start;
        let ghost old_end = self.range@.end;
        let ghost old_view_g = self.mem_view;
        let ghost split_end = old_start + nbytes;

        let tracked old_view = self.mem_view.tracked_take();
        let tracked left_view = match old_view {
            VmIoMemView::WriteView(view) => {
                let ghost view_g = view;
                let tracked (left, right) = view.split(old_start, nbytes);
                MemView::lemma_split_preserves_transl(view_g, old_start, nbytes, left, right);
                // Prove both halves preserve mappings invariants and translation.
                assert(left.mappings.finite());
                assert(left.mappings_are_disjoint()) by {
                    assert(left.mappings <= view_g.mappings);
                };
                assert forall|va: usize| old_start <= va < split_end implies
                    #[trigger] left.addr_transl(va) is Some by {
                    assert(view_g.addr_transl(va) is Some);
                    assert(view_g.addr_transl(va) == left.addr_transl(va));
                };
                assert(right.mappings.finite());
                assert(right.mappings_are_disjoint()) by {
                    assert(right.mappings <= view_g.mappings);
                };
                assert forall|va: usize| split_end <= va < old_end implies
                    #[trigger] right.addr_transl(va) is Some by {
                    assert(view_g.addr_transl(va) is Some);
                    assert(view_g.addr_transl(va) == right.addr_transl(va));
                };
                self.mem_view = Some(VmIoMemView::WriteView(right));
                VmIoMemView::WriteView(left)
            },
            VmIoMemView::ReadView(view) => {
                let ghost view_g = view;
                let tracked (left, right) = view.split(old_start, nbytes);
                MemView::lemma_split_preserves_transl(view_g, old_start, nbytes, left, right);
                assert(left.mappings.finite());
                assert(left.mappings_are_disjoint()) by {
                    assert(left.mappings <= view_g.mappings);
                };
                assert forall|va: usize| old_start <= va < split_end implies
                    #[trigger] left.addr_transl(va) is Some by {
                    assert(view_g.addr_transl(va) is Some);
                    assert(view_g.addr_transl(va) == left.addr_transl(va));
                };
                assert(right.mappings.finite());
                assert(right.mappings_are_disjoint()) by {
                    assert(right.mappings <= view_g.mappings);
                };
                assert forall|va: usize| split_end <= va < old_end implies
                    #[trigger] right.addr_transl(va) is Some by {
                    assert(view_g.addr_transl(va) is Some);
                    assert(view_g.addr_transl(va) == right.addr_transl(va));
                };
                // If the original read view was fully initialized, both halves
                // remain initialized on their respective ranges.
                if old_view_g matches Some(VmIoMemView::ReadView(mv0))
                    && (forall|i: usize|
                        #![trigger mv0.addr_transl(i)]
                        old_start <= i < old_end ==> {
                            &&& mv0.addr_transl(i) is Some
                            &&& mv0.memory.contains_key(mv0.addr_transl(i).unwrap().0)
                            &&& mv0.memory[mv0.addr_transl(i).unwrap().0].contents
                                [mv0.addr_transl(i).unwrap().1 as int] is Init
                        })
                {
                    assert forall|i: usize|
                        #![trigger left.addr_transl(i)]
                        old_start <= i < split_end implies {
                            &&& left.addr_transl(i) is Some
                            &&& left.memory.contains_key(left.addr_transl(i).unwrap().0)
                            &&& left.memory[left.addr_transl(i).unwrap().0].contents
                                [left.addr_transl(i).unwrap().1 as int] is Init
                        } by {
                        assert(view_g.addr_transl(i) == left.addr_transl(i));
                        let pa = left.addr_transl(i).unwrap().0;
                        assert(view_g.memory.contains_key(pa));
                        assert(view_g.is_mapped(i, pa));
                        assert(left.memory.dom().contains(pa));
                        assert(left.memory[pa] == view_g.memory[pa]);
                    };
                    assert forall|i: usize|
                        #![trigger right.addr_transl(i)]
                        split_end <= i < old_end implies {
                            &&& right.addr_transl(i) is Some
                            &&& right.memory.contains_key(right.addr_transl(i).unwrap().0)
                            &&& right.memory[right.addr_transl(i).unwrap().0].contents
                                [right.addr_transl(i).unwrap().1 as int] is Init
                        } by {
                        assert(view_g.addr_transl(i) == right.addr_transl(i));
                        let pa = right.addr_transl(i).unwrap().0;
                        assert(view_g.memory.contains_key(pa));
                        assert(view_g.is_mapped(i, pa));
                        assert(right.memory.dom().contains(pa));
                        assert(right.memory[pa] == view_g.memory[pa]);
                    };
                }
                self.mem_view = Some(VmIoMemView::ReadView(right));
                VmIoMemView::ReadView(left)
            },
        };
        self.range = Ghost(Range { start: split_end as usize, end: old_end });

        let tracked left_owner = VmIoOwner {
            id: Ghost(arbitrary()),
            range: Ghost(Range { start: old_start, end: split_end as usize }),
            is_fallible: self.is_fallible,
            is_kernel: self.is_kernel,
            mem_view: Some(left_view),
        };
        left_owner
    }

    /// Unwraps the read view.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The owner must carry a read memory view.
    /// ## Postconditions
    /// - The returned reference is exactly the read view stored in `self.mem_view`.
    pub proof fn tracked_read_view_unwrap(tracked &self) -> (tracked r: &MemView)
        requires
            self.inv(),
            self.mem_view matches Some(VmIoMemView::ReadView(_)),
        ensures
            VmIoMemView::ReadView(*r) == self.mem_view.unwrap(),
    {
        match &self.mem_view {
            Some(VmIoMemView::ReadView(r)) => r,
            _ => { proof_from_false() },
        }
    }

    /// Converts the owner's [`VmIoMemView::WriteView`] into a [`VmIoMemView::ReadView`]
    /// wrapping the same underlying [`MemView`].
    ///
    /// Used after a write-only phase (e.g., [`VmWriter::fill`]) to hand the buffer
    /// back as a read-only handle.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant and carry a write memory view.
    /// ## Postconditions
    /// - The owner still satisfies its invariant.
    /// - All structural fields (`range`, `is_fallible`, `is_kernel`, `id`) are preserved.
    /// - The memory view is now [`VmIoMemView::ReadView`] wrapping the same [`MemView`]
    ///   as the original [`VmIoMemView::WriteView`].
    pub proof fn write_to_read(tracked &mut self)
        requires
            old(self).inv(),
            old(self).mem_view matches Some(VmIoMemView::WriteView(_)),
        ensures
            final(self).inv(),
            final(self).range@ == old(self).range@,
            final(self).is_fallible == old(self).is_fallible,
            final(self).is_kernel == old(self).is_kernel,
            final(self).id == old(self).id,
            final(self).mem_view matches Some(VmIoMemView::ReadView(_)),
            old(self).mem_view matches Some(VmIoMemView::WriteView(mv)) ==>
                final(self).mem_view matches Some(VmIoMemView::ReadView(rv)) && rv == mv,
    {
        let tracked old_view = self.mem_view.tracked_take();
        let tracked mv = match old_view {
            VmIoMemView::WriteView(m) => m,
            _ => { proof_from_false() },
        };
        self.mem_view = Some(VmIoMemView::ReadView(mv));
    }
}

// =============================================================================
// wf/inv relating exec readers/writers to their ghost owners
// =============================================================================

impl<Fallibility> VmWriter<'_, Fallibility> {
    /// Structural well-formedness: cursor and end share the same ghost range.
    pub open spec fn inv_wf(self) -> bool {
        &&& self.cursor.range@ == self.end.range@
    }

    /// Relates a concrete writer to its ghost owner.
    pub open spec fn wf(self, owner: VmIoOwner) -> bool {
        &&& owner.inv()
        &&& owner.range@.start == self.cursor.vaddr
        &&& owner.range@.end == self.end.vaddr
        &&& owner.id == self.id
        &&& owner.mem_view matches Some(VmIoMemView::WriteView(mv)) ==> {
            forall|va: usize|
                owner.range@.start <= va < owner.range@.end ==> {
                    &&& #[trigger] mv.addr_transl(va) is Some
                }
        }
    }
}

impl<Fallibility> Inv for VmWriter<'_, Fallibility> {
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr <= self.end.vaddr
    }
}

impl<Fallibility> VmReader<'_, Fallibility> {
    /// Structural well-formedness: cursor and end share the same ghost range.
    pub open spec fn inv_wf(self) -> bool {
        &&& self.cursor.range@ == self.end.range@
    }

    /// Relates a concrete reader to its ghost owner.
    pub open spec fn wf(self, owner: VmIoOwner) -> bool {
        &&& owner.inv()
        &&& owner.range@.start == self.cursor.vaddr
        &&& owner.range@.end == self.end.vaddr
        &&& owner.id == self.id
        &&& owner.mem_view matches Some(VmIoMemView::ReadView(mv)) ==> {
            forall|va: usize|
                owner.range@.start <= va < owner.range@.end ==> {
                    &&& #[trigger] mv.addr_transl(va) is Some
                }
        }
    }
}

impl<Fallibility> Inv for VmReader<'_, Fallibility> {
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr <= self.end.vaddr
    }
}

} // verus!
