use vstd::pervasive::proof_from_false;
use vstd::prelude::*;

use vstd_extra::ownership::*;
use crate::mm::io::{VmIoOwner, VmIoMemView};
use crate::mm::vm_space::{UserPtConfig, VmSpace};
use crate::mm::{Paddr, Vaddr};
use crate::specs::mm::page_table::{Guards, Mapping, OwnerSubtree, PageTableOwner, PageTableView};
use crate::specs::mm::tlb::TlbModel;
use crate::specs::mm::virt_mem_newer::{FrameContents, MemView};

verus! {

/// This struct is used for reading/writing memories represented by the
/// [`VmReader`] or [`VmWriter`]. We also require a valid `vmspace_owner`
/// must be present in this struct to ensure that the reader/writer is
/// not created out of thin air.
pub tracked struct VmIoPermission<'a> {
    pub vmio_owner: VmIoOwner<'a>,
    pub vmspace_owner: VmSpaceOwner<'a>,
}

/// A tracked struct for reasoning about verification-only properties of a [`VmSpace`].
pub tracked struct VmSpaceOwner<'a> {
    /// The owner of the page table of this VM space.
    pub page_table_owner: OwnerSubtree<UserPtConfig>,
    /// Whether this VM space is currently active.
    pub active: bool,
    /// Active readers for this VM space.
    pub readers: Seq<VmIoOwner<'a>>,
    /// Active writers for this VM space.
    pub writers: Seq<VmIoOwner<'a>>,
    /// The "actual" memory view of this VM space where some
    /// of the mappings may be  transferred to the writers.
    pub mem_view: Option<MemView>,
    /// This is the holistic view of the memory range covered by this VM space owner.
    pub mv_range: Ghost<Option<MemView>>,
    /// Whether we allow shared reading.
    pub shared_reader: bool,
}

impl<'a> Inv for VmSpaceOwner<'a> {
    /// Defines the invariant for `VmSpaceOwner`.
    ///
    /// This specification ensures the consistency of the VM space, particularly
    /// regarding memory access permissions and overlapping ranges.
    ///
    /// # Invariants
    /// 1. **Recursion**: The underlying `page_table_owner` must satisfy its own invariant.
    /// 2. **Finiteness**: The sets of readers and writers must be finite.
    /// 3. **Active State Consistency**: If the VM space is marked as `active`:
    ///    - **ID Separation**: A handle ID cannot be both a reader and a writer simultaneously.
    ///    - **Element Validity**: All stored `VmIoOwner` instances must be valid and
    ///                             their stored ID must match their map key.
    ///    - **Memory Isolation (Read-Write)**: No Reader memory range may overlap with any Writer memory range.
    ///    - **Memory Isolation (Write-Write)**: No Writer memory range may overlap with any other Writer memory range.
    ///    - **Conditional Read Isolation**: If `shared_reader` is set, Readers must be mutually disjoint (cannot overlap).
    open spec fn inv(self) -> bool {
        &&& self.page_table_owner.inv()
        &&& self.active ==> {
            &&& self.mem_view_wf()
            &&& self.mem_view matches Some(mem_view) ==> {
                // Readers and writers are valid.
                &&& forall|i: int|
                    #![trigger self.readers[i]]
                    0 <= i < self.readers.len() as int ==> {
                        &&& self.readers[i].inv()
                    }
                &&& forall|i: int|
                    #![trigger self.writers[i]]
                    0 <= i < self.writers.len() as int ==> {
                        &&& self.writers[i].inv()
                    }
                    // --- Memory Range Overlap Checks ---
                    // Readers do not overlap with other readers, and writers do not overlap with other writers.
                &&& forall|i, j: int|
                    #![trigger self.readers[i], self.writers[j]]
                    0 <= i < self.readers.len() as int && 0 <= j < self.writers.len() as int ==> {
                        let r = self.readers[i];
                        let w = self.writers[j];
                        r.disjoint(w)
                    }
                &&& !self.shared_reader ==> forall|i, j: int|
                    #![trigger self.readers[i], self.readers[j]]
                    0 <= i < self.readers.len() as int && 0 <= j < self.readers.len() as int && i
                        != j ==> {
                        let r1 = self.readers[i];
                        let r2 = self.readers[j];
                        r1.disjoint(r2)
                    }
                &&& forall|i, j: int|
                    #![trigger self.writers[i], self.writers[j]]
                    0 <= i < self.writers.len() as int && 0 <= j < self.writers.len() as int && i
                        != j ==> {
                        let w1 = self.writers[i];
                        let w2 = self.writers[j];
                        w1.disjoint(w2)
                    }
            }
        }
    }
}

impl<'a> VmSpaceOwner<'a> {
    pub open spec fn mem_view_wf(self) -> bool {
        &&& self.mem_view is Some
            <==> self.mv_range@ is Some
        // This requires that TotalMapping (mvv) = mv ∪ writer mappings ∪ reader mappings
        &&& self.mem_view matches Some(remaining_view) ==> self.mv_range@ matches Some(total_view)
            ==> {
            &&& remaining_view.mappings_are_disjoint()
            &&& remaining_view.mappings.finite()
            &&& total_view.mappings_are_disjoint()
            &&& total_view.mappings.finite()
            // ======================
            // Remaining Consistency
            // ======================
            &&& remaining_view.mappings.subset_of(total_view.mappings)
            &&& remaining_view.memory.dom().subset_of(
                total_view.memory.dom(),
            )
            // =====================
            // Total View Consistency
            // =====================
            &&& forall|va: usize|
                #![trigger remaining_view.addr_transl(va)]
                #![trigger total_view.addr_transl(va)]
                remaining_view.addr_transl(va) == total_view.addr_transl(
                    va,
                )
            // =====================
            // Writer correctness
            // =====================
            &&& forall|i: int|
                #![trigger self.writers[i]]
                0 <= i < self.writers.len() as int ==> {
                    let writer = self.writers[i];

                    &&& writer.mem_view matches Some(VmIoMemView::WriteView(writer_mv)) && {
                        &&& forall|va: usize|
                            #![trigger writer_mv.addr_transl(va)]
                            #![trigger total_view.addr_transl(va)]
                            #![trigger remaining_view.addr_transl(va)]
                            #![trigger remaining_view.memory.contains_key(va)]
                            {
                                // We do not enforce that the range must be the same as the
                                // memory view it holds as the writer may not consume all the
                                // memory in its range.
                                //
                                // So we cannot directly reason on `self.range` here; we need
                                // to instead ensure that the memory view it holds is consistent
                                // with the total view and remaining view.
                                &&& writer_mv.mappings.finite()
                                &&& writer_mv.addr_transl(va) == total_view.addr_transl(va)
                                &&& writer_mv.addr_transl(va) matches Some(_) ==> {
                                    &&& remaining_view.addr_transl(va) is None
                                    &&& !remaining_view.memory.contains_key(va)
                                }
                            }
                        &&& writer_mv.mappings.disjoint(remaining_view.mappings)
                        &&& writer_mv.mappings.subset_of(total_view.mappings)
                        &&& writer_mv.memory.dom().subset_of(total_view.memory.dom())
                    }
                }
                // =====================
                // Reader correctness
                // =====================
            &&& forall|i: int|
                #![trigger self.readers[i]]
                0 <= i < self.readers.len() as int ==> {
                    let reader = self.readers[i];

                    &&& reader.mem_view matches Some(VmIoMemView::ReadView(reader_mv)) && {
                        forall|va: usize|
                            #![trigger reader_mv.addr_transl(va)]
                            #![trigger total_view.addr_transl(va)]
                            {
                                // For readers there is no need to check remaining_view
                                // because it is borrowed from remaining_view directly.
                                &&& reader_mv.mappings.finite()
                                &&& reader_mv.addr_transl(va) == total_view.addr_transl(va)
                            }
                    }
                }
        }
    }

    /// The basic invariant between a VM space and its owner.
    pub open spec fn inv_with(&self, vm_space: VmSpace<'a>) -> bool {
        &&& self.shared_reader == vm_space.shared_reader
        &&& self.readers.len() == vm_space.readers@.len()
        &&& self.writers.len() == vm_space.writers@.len()
        &&& forall|i: int|
            #![trigger self.readers[i]]
            #![trigger vm_space.readers@[i]]
            0 <= i < vm_space.readers@.len() as int ==> {
                &&& self.readers[i].inv_with_reader(*vm_space.readers@[i])
            }
        &&& forall|i: int|
            #![trigger self.writers[i]]
            #![trigger vm_space.writers@[i]]
            0 <= i < vm_space.writers@.len() as int ==> {
                &&& self.writers[i].inv_with_writer(*vm_space.writers@[i])
            }
    }

    /// Checks if we can create a new reader under this VM space owner.
    ///
    /// This requires no active writers overlapping with the new reader.
    pub open spec fn can_create_reader(&self, vaddr: Vaddr, len: usize) -> bool
        recommends
            self.inv(),
    {
        &&& forall|i: int|
            #![trigger self.writers[i]]
            0 <= i < self.writers.len() ==> !self.writers[i].overlaps_with_range(
                vaddr..(vaddr + len) as usize,
            )
    }

    /// Checks if we can create a new writer under this VM space owner.
    ///
    /// Similar to [`can_create_reader`], but checks both active readers and writers.
    pub open spec fn can_create_writer(&self, vaddr: Vaddr, len: usize) -> bool
        recommends
            self.inv(),
    {
        &&& forall|i: int|
            #![trigger self.readers[i]]
            0 <= i < self.readers.len() ==> !self.readers[i].overlaps_with_range(
                vaddr..(vaddr + len) as usize,
            )
        &&& forall|i: int|
            #![trigger self.writers[i]]
            0 <= i < self.writers.len() ==> !self.writers[i].overlaps_with_range(
                vaddr..(vaddr + len) as usize,
            )
    }

    // /// Generates a new unique ID for VM IO owners.
    // ///
    // /// This assumes that we always generate a fresh ID that is not used by any existing
    // /// readers or writers. This should be safe as the ID space is unbounded and only used
    // /// to reason about different VM IO owners in verification.
    #[verus_spec(r =>
        requires
            self.inv(),
    )]
    pub axiom fn new_vm_io_id(&self) -> nat;

    /// Removes the given reader from the active readers list.
    pub proof fn remove_reader(tracked &mut self, idx: int)
        requires
            old(self).inv(),
            old(self).active,
            old(self).mem_view is Some,
            0 <= idx < old(self).readers.len() as int,
        ensures
            self.inv(),
            self.active == old(self).active,
            self.shared_reader == old(self).shared_reader,
            self.readers == old(self).readers.remove(idx),
    {
        self.readers.tracked_remove(idx);
    }

    /// Disposes the given reader, releasing its ownership on the memory range.
    ///
    /// This does not mean that the owner is discarded; it indicates that someone
    /// who finishes the reading operation can let us reclaim the permission.
    /// The deletion of the reader is done via another API [`VmSpaceOwner::remove_reader`].
    ///
    /// Typically this API is called in two scenarios:
    ///
    /// 1. The reader has been created and we immediately move the ownership into us.
    /// 2. The reader has finished the reading and need to return the ownership back.
    pub proof fn dispose_reader(tracked &mut self, tracked owner: VmIoOwner<'a>)
        requires
            owner.inv(),
            old(self).inv(),
            old(self).active,
            old(self).mv_range@ matches Some(total_view) && owner.mem_view matches Some(
                VmIoMemView::ReadView(mv),
            ) && old(self).mem_view matches Some(remaining) && mv.mappings.finite() && {
                forall|va: usize|
                    #![auto]
                    {
                        &&& total_view.addr_transl(va) == mv.addr_transl(va)
                        &&& mv.mappings.finite()
                    }
            },
            forall|i: int|
                #![trigger old(self).writers[i]]
                0 <= i < old(self).writers.len() ==> old(self).writers[i].disjoint(owner),
            forall|i: int|
                #![trigger old(self).readers[i]]
                0 <= i < old(self).readers.len() ==> old(self).readers[i].disjoint(owner),
        ensures
            self.inv(),
            self.active == old(self).active,
            self.shared_reader == old(self).shared_reader,
            owner.range@.start < owner.range@.end ==> self.readers == old(self).readers.push(owner),
    {
        let tracked mv = match owner.mem_view {
            Some(VmIoMemView::ReadView(mv)) => mv,
            _ => { proof_from_false() },
        };

        if owner.range@.start < owner.range@.end {
            // Return the memory view back to the vm space owner.
            self.readers.tracked_push(owner);
        }
    }

    /// Disposes the given writer, releasing its ownership on the memory range.
    ///
    /// This does not mean that the owner is discarded; it indicates that someone
    /// who finishes the writing operation can let us reclaim the permission.
    ///
    /// The deletion of the writer is through another API [`VmSpaceOwner::remove_writer`].
    pub proof fn dispose_writer(tracked &mut self, tracked owner: VmIoOwner<'a>)
        requires
            old(self).inv(),
            old(self).active,
            owner.inv(),
            old(self).mv_range@ matches Some(total_view) && owner.mem_view matches Some(
                VmIoMemView::WriteView(mv),
            ) && old(self).mem_view matches Some(remaining) && mv.mappings.finite() && {
                &&& forall|va: usize|
                    #![auto]
                    {
                        &&& mv.addr_transl(va) == total_view.addr_transl(va)
                        &&& mv.addr_transl(va) matches Some(_) ==> {
                            &&& remaining.addr_transl(va) is None
                            &&& !remaining.memory.contains_key(va)
                        }
                    }
                &&& mv.mappings.disjoint(remaining.mappings)
                &&& mv.mappings.subset_of(total_view.mappings)
                &&& mv.memory.dom().subset_of(total_view.memory.dom())
            },
            forall|i: int|
                #![trigger old(self).writers[i]]
                0 <= i < old(self).writers.len() as int ==> old(self).writers[i].disjoint(owner),
            forall|i: int|
                #![trigger old(self).readers[i]]
                0 <= i < old(self).readers.len() as int ==> old(self).readers[i].disjoint(owner),
        ensures
            self.inv(),
            self.active == old(self).active,
            self.shared_reader == old(self).shared_reader,
            owner.range@.start < owner.range@.end ==> self.writers == old(self).writers.push(owner),
    {
        // If the writer has consumed all the memory, nothing to do;
        // just discard the writer and return the permission back to
        // the vm space owner.
        match owner.mem_view {
            Some(VmIoMemView::WriteView(ref writer_mv)) => {
                if owner.range@.start < owner.range@.end {
                    self.writers.tracked_push(owner);
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn remove_writer(tracked &mut self, idx: usize)
        requires
            old(self).inv(),
            old(self).active,
            old(self).mem_view is Some,
            old(self).mv_range@ is Some,
            0 <= idx < old(self).writers.len() as int,
        ensures
            self.inv(),
            self.active == old(self).active,
            self.shared_reader == old(self).shared_reader,
            self.writers == old(self).writers.remove(idx as int),
    {
        let tracked writer = self.writers.tracked_remove(idx as int);

        // Now we need to "return" the memory view back to the vm space owner.
        let tracked mv = match writer.mem_view {
            Some(VmIoMemView::WriteView(mv)) => mv,
            _ => { proof_from_false() },
        };

        // "Join" the memory view back.
        let tracked mut remaining = self.mem_view.tracked_take();
        let ghost old_remaining = remaining;
        remaining.join(mv);
        self.mem_view = Some(remaining);

        assert(self.mem_view_wf()) by {
            let ghost total_view = self.mv_range@.unwrap();

            assert(remaining.mappings =~= old_remaining.mappings.union(mv.mappings));
            assert(remaining.memory =~= old_remaining.memory.union_prefer_right(mv.memory));
            assert(self.mv_range == old(self).mv_range);
            assert(self.mem_view == Some(remaining));

            assert forall|va: usize|
                #![auto]
                { remaining.addr_transl(va) == total_view.addr_transl(va) } by {
                let r_mappings = remaining.mappings.filter(
                    |m: Mapping| m.va_range.start <= va < m.va_range.end,
                );
                let t_mappings = total_view.mappings.filter(
                    |m: Mapping| m.va_range.start <= va < m.va_range.end,
                );
                let w_mappings = mv.mappings.filter(
                    |m: Mapping| m.va_range.start <= va < m.va_range.end,
                );

                assert(r_mappings.subset_of(t_mappings));
                assert(w_mappings.subset_of(t_mappings));

                if r_mappings.len() > 0 {
                    assert(t_mappings.len() > 0) by {
                        let r = r_mappings.choose();
                        assert(r_mappings.contains(r)) by {
                            vstd::set::axiom_set_choose_len(r_mappings);
                        }
                        assert(t_mappings.contains(r));
                    }
                }
            }

            assert forall|i: int|
                #![trigger self.writers[i]]
                0 <= i < self.writers.len() as int implies {
                let other_writer = self.writers[i];

                &&& other_writer.mem_view matches Some(VmIoMemView::WriteView(writer_mv))
                    && writer_mv.mappings.disjoint(remaining.mappings)
            } by {
                let other_writer = self.writers[i];

                assert(old(self).inv());
                let writer_mv = match other_writer.mem_view {
                    Some(VmIoMemView::WriteView(mv)) => mv,
                    _ => { proof_from_false() },
                };

                assert(mv.mappings.disjoint(writer_mv.mappings)) by {
                    assert(exists|i: int|
                        0 <= i < old(self).writers.len() as int ==> #[trigger] old(self).writers[i]
                            == other_writer);
                    assert(exists|i: int|
                        0 <= i < old(self).writers.len() as int ==> #[trigger] old(self).writers[i]
                            == writer);
                }
            }
        }
    }
}
}
