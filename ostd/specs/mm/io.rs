// SPDX-License-Identifier: MPL-2.0
//! Specification helpers for [`crate::mm::io`].
//!
//! The tracked VM I/O owner/view types live in `crate::mm::io`. This module only
//! adds spec/proof impls for the exec reader/writer types.
use core::{marker::PhantomData, ops::Range};

use vstd::pervasive::arbitrary;
use vstd::prelude::*;
use vstd::std_specs::convert::FromSpecImpl;
use vstd_extra::ownership::Inv;

use crate::mm::io::{Infallible, VmReader, VmWriter};

use super::virt_mem_newer::MemView;

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
    /// Whether this reader is fallible.
    pub is_fallible: bool,
    pub phantom: PhantomData<&'a [u8]  /*, Fallibility)*/ >,
    /// Whether this owner is for kernel space.
    pub is_kernel: bool,
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
    #[verifier::external_body]
    pub proof fn advance(tracked &mut self, nbytes: usize) -> (tracked res: VmIoMemView<'_>)
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
        arbitrary()
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
        match &self.mem_view {
            Some(VmIoMemView::ReadView(r)) => r,
            _ => { proof_from_false() },
        }
    }
}

impl<Fallibility> VmWriter<'_, Fallibility> {
    /// Structural well-formedness: cursor and end share the same ghost range.
    pub open spec fn inv_wf(self) -> bool {
        &&& self.cursor.range@ == self.end.range@
    }

    /// Relates a concrete writer to its ghost owner.
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
    open spec fn inv(self) -> bool {
        &&& self.inv_wf()
        &&& self.cursor.inv()
        &&& self.end.inv()
        &&& self.cursor.vaddr <= self.end.vaddr
    }
}

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
