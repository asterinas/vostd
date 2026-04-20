// SPDX-License-Identifier: MPL-2.0
//! Specification types and ghost state for [`crate::mm::io`].
//!
//! This module hosts the tracked types ([`VmIoOwner`], [`VmIoMemView`]) and
//! the spec/proof impls for the exec types ([`VmReader`], [`VmWriter`]).
use core::marker::PhantomData;
use core::ops::Range;
use vstd::pervasive::proof_from_false;
use vstd::prelude::*;
use vstd::std_specs::convert::FromSpecImpl;
use vstd_extra::ownership::Inv;

use crate::mm::io::{Infallible, VmReader, VmWriter};
use crate::specs::mm::page_table::Mapping;
use crate::specs::mm::virt_mem_newer::{MemView, VirtPtr};

verus! {

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
/// ⚠️ WARNING: We do not recommend using this enum directly.
///
/// [`VmSpaceOwner`]: crate::mm::vm_space::VmSpaceOwner
pub tracked enum VmIoMemView<'a> {
    /// An owned memory for writing.
    WriteView(MemView),
    /// A shared memory for reading.
    ReadView(&'a MemView),
}

/// The owner of a VM I/O operation, which tracks the memory range and the memory view for the
/// operation.
///
/// Basically the caller should be only interested in this struct when using [`VmReader`] and
/// [`VmWriter`] to perform VM I/O operations, since the safety of these operations depends on the
/// validity of the memory range and memory view tracked by this struct.
pub tracked struct VmIoOwner<'a> {
    /// The unique identifier of this owner.
    pub id: Ghost<nat>,
    /// The virtual address range owned by this owner.
    pub range: Ghost<Range<usize>>,
    /// The mem view associated with this owner.
    pub phantom: PhantomData<&'a [u8]>,
    /// The mem view associated with this owner.
    pub mem_view: Option<VmIoMemView<'a>>,
}

impl VmIoOwner<'_> {
    /// Structural well-formedness: the range is ordered.
    /// Always holds after construction.
    pub open spec fn inv_wf(self) -> bool {
        self.range@.start <= self.range@.end
    }
}

impl Inv for VmIoOwner<'_> {
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

impl VmIoOwner<'_> {
    /// Checks whether this owner overlaps with another owner.
    #[verifier::inline]
    pub open spec fn overlaps(self, other: VmIoOwner<'_>) -> bool {
        !self.disjoint(other)
    }

    #[verifier::inline]
    pub open spec fn overlaps_with_range(self, range: Range<usize>) -> bool {
        &&& self.range@.start <= range.end
        &&& range.start <= self.range@.end
    }

    /// Checks whether this owner is disjoint with another owner.
    #[verifier::inline]
    pub open spec fn disjoint(self, other: VmIoOwner<'_>) -> bool {
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
    pub open spec fn params_eq(self, other: VmIoOwner<'_>) -> bool {
        &&& self.range@ == other.range@
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
    pub proof fn advance(tracked &mut self, nbytes: usize) -> (tracked res: VmIoMemView<'_>)
        requires
            old(self).inv(),
            old(self).mem_view is Some,
            nbytes <= old(self).range@.end - old(self).range@.start,
        ensures
            final(self).inv(),
            final(self).range@.start == old(self).range@.start + nbytes,
            final(self).range@.end == old(self).range@.end,
            final(self).id == old(self).id,
    {
        let start = self.range@.start;
        let old_end = self.range@.end;
        self.range = Ghost((start + nbytes) as usize..self.range@.end);
        let tracked inner = self.mem_view.tracked_take();
        let tracked ret_perm = match inner {
            VmIoMemView::WriteView(mv) => {
                let tracked (lhs, rhs) = mv.split(start, nbytes);

                assert(forall|va: usize|
                    start <= va < start + nbytes ==> mv.addr_transl(va) is Some);

                self.mem_view = Some(VmIoMemView::WriteView(rhs));

                assert(self.inv()) by {
                    broadcast use vstd::set::group_set_axioms;
                    assert(old(self).inv());
                    assert forall|va: usize| start + nbytes <= va < old_end implies {
                        #[trigger] rhs.addr_transl(va) is Some
                    } by {
                        assert(mv.addr_transl(va) is Some);

                        let old_mappings = mv.mappings.filter(
                            |m: Mapping| m.va_range.start <= va < m.va_range.end,
                        );
                        let new_mappings = rhs.mappings.filter(
                            |m: Mapping| m.va_range.start <= va < m.va_range.end,
                        );
                        assert(old_mappings.len() != 0);
                        assert(rhs.mappings =~= mv.mappings.filter(
                            |m: Mapping| m.va_range.end > start + nbytes,
                        ));
                        assert(new_mappings =~= mv.mappings.filter(
                            |m: Mapping|
                                m.va_range.start <= va < m.va_range.end && m.va_range.end > start
                                    + nbytes,
                        ));

                        let m = old_mappings.choose();
                        assert(start + nbytes <= va);
                        if (m.va_range.end <= va) {
                            assert(!old_mappings.contains(m));
                        }
                        assert(m.va_range.end > va);
                        assert(m.va_range.end > start + nbytes);
                        assert(old_mappings.contains(m));
                        assert(old_mappings.subset_of(mv.mappings));
                        assert(rhs.mappings.contains(m));
                        assert(new_mappings.contains(m));
                        assert(new_mappings.len() >= 1);
                        assert(new_mappings.len() != 0);
                    }
                }

                VmIoMemView::WriteView(lhs)
            },
            VmIoMemView::ReadView(mv) => {
                let tracked sub_view = mv.borrow_at(start, nbytes);
                self.mem_view = Some(VmIoMemView::ReadView(mv));
                VmIoMemView::ReadView(sub_view)
            },
        };

        ret_perm
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
            VmIoMemView::ReadView(r) == self.mem_view.unwrap(),
    {
        match self.mem_view {
            Some(VmIoMemView::ReadView(r)) => r,
            _ => { proof_from_false() },
        }
    }

    /// Returns a shared reference to the write view.
    ///
    /// # Verified Properties
    /// ## Preconditions
    /// - The owner must satisfy its invariant.
    /// - The owner must carry a write memory view.
    /// ## Postconditions
    /// - The returned reference is exactly the write view stored in `self.mem_view`.
    pub proof fn tracked_write_view_unwrap(tracked &self) -> (tracked r: &MemView)
        requires
            self.inv(),
            self.mem_view matches Some(VmIoMemView::WriteView(_)),
        ensures
            VmIoMemView::WriteView(*r) == self.mem_view.unwrap(),
    {
        match &self.mem_view {
            Some(VmIoMemView::WriteView(mv)) => mv,
            _ => { proof_from_false() },
        }
    }
}

impl<Fallibility> VmWriter<'_, Fallibility> {
    pub open spec fn avail_spec(&self) -> usize {
        (self.end.vaddr - self.cursor.vaddr) as usize
    }

    /// Structural well-formedness: cursor and end share the same ghost range.
    /// Always holds after construction, regardless of input validity.
    pub open spec fn inv_wf(self) -> bool {
        &&& self.cursor.range@ == self.end.range@
    }

    /// Relates a concrete [`VmWriter`] to its ghost [`VmIoOwner`],
    /// following the `OwnerOf::wf` pattern.
    pub open spec fn wf(self, owner: VmIoOwner<'_>) -> bool {
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
    /// Full invariant: well-formed AND semantically valid (non-null, ordered).
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr <= self.end.vaddr
    }
}

impl<Fallibility> VmReader<'_, Fallibility> {
    pub open spec fn remain_spec(&self) -> usize {
        (self.end.vaddr - self.cursor.vaddr) as usize
    }

    /// Structural well-formedness: cursor and end share the same ghost range.
    /// Always holds after construction, regardless of input validity.
    pub open spec fn inv_wf(self) -> bool {
        &&& self.cursor.range@ == self.end.range@
    }

    /// Relates a concrete [`VmReader`] to its ghost [`VmIoOwner`],
    /// following the `OwnerOf::wf` pattern.
    pub open spec fn wf(self, owner: VmIoOwner<'_>) -> bool {
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
    /// Full invariant: well-formed AND semantically valid (non-null, ordered).
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr <= self.end.vaddr
    }
}

// The `From<&[u8]>` and `From<&mut [u8]>` impls on `VmReader`/`VmWriter` delegate
// to the external-body helpers `from_slice`/`from_slice_mut`, so we opt out of
// the spec-level agreement by declaring `obeys_from_spec() == false`.

impl<'a> FromSpecImpl<&'a [u8]> for VmReader<'a, Infallible> {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(_slice: &'a [u8]) -> Self {
        arbitrary()
    }
}

impl<'a> FromSpecImpl<&'a mut [u8]> for VmWriter<'a, Infallible> {
    open spec fn obeys_from_spec() -> bool {
        false
    }

    open spec fn from_spec(_slice: &'a mut [u8]) -> Self {
        arbitrary()
    }
}

} // verus!
