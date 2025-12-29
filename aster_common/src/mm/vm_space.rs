use vstd::prelude::*;

use vstd::simple_pptr::*;
use vstd_extra::ownership::Inv;

use crate::frame::{AnyFrameMeta, Frame, UFrame};
use crate::page_table::*;
use crate::*;

use core::ops::Range;

use std::marker::PhantomData;

verus! {

#[derive(Clone, Debug)]
pub struct UserPtConfig {}

/// The item that can be mapped into the [`VmSpace`].
#[derive(Clone)]
pub struct MappedItem {
    pub frame: UFrame,
    pub prop: PageProperty,
}

// SAFETY: `item_into_raw` and `item_from_raw` are implemented correctly,
unsafe impl PageTableConfig for UserPtConfig {
    open spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize> {
        0..256
    }

    fn TOP_LEVEL_INDEX_RANGE() -> Range<usize> {
        0..256
    }

    fn TOP_LEVEL_CAN_UNMAP() -> (b: bool) {
        true
    }

    type E = PageTableEntry;

    type C = PagingConsts;

    type Item = MappedItem;

    #[verifier::external_body]
    fn item_into_raw(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        unimplemented!()/*
        let (frame, prop) = item;
        let level = frame.map_level();
        let paddr = frame.into_raw();
        (paddr, level, prop)
        */

    }

    uninterp spec fn item_from_raw_spec(
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
    ) -> Self::Item;

    #[verifier::external_body]
    fn item_from_raw(paddr: Paddr, level: PagingLevel, prop: PageProperty) -> Self::Item {
        unimplemented!()/*
        debug_assert_eq!(level, 1);
        // SAFETY: The caller ensures safety.
        let frame = unsafe { Frame::<dyn AnyUFrameMeta>::from_raw(paddr) };
        (frame, prop)
        */

    }
}

/// A virtual address space for user-mode tasks, enabling safe manipulation of user-space memory.
///
/// The `VmSpace` type provides memory isolation guarantees between user-space and
/// kernel-space. For example, given an arbitrary user-space pointer, one can read and
/// write the memory location referred to by the user-space pointer without the risk of
/// breaking the memory safety of the kernel space.
///
/// # Task Association Semantics
///
/// As far as OSTD is concerned, a `VmSpace` is not necessarily associated with a task. Once a
/// `VmSpace` is activated (see [`VmSpace::activate`]), it remains activated until another
/// `VmSpace` is activated **possibly by another task running on the same CPU**.
///
/// This means that it's up to the kernel to ensure that a task's `VmSpace` is always activated
/// while the task is running. This can be done by using the injected post schedule handler
/// (see [`inject_post_schedule_handler`]) to always activate the correct `VmSpace` after each
/// context switch.
///
/// If the kernel otherwise decides not to ensure that the running task's `VmSpace` is always
/// activated, the kernel must deal with race conditions when calling methods that require the
/// `VmSpace` to be activated, e.g., [`UserMode::execute`], [`VmSpace::reader`],
/// [`VmSpace::writer`]. Otherwise, the behavior is unspecified, though it's guaranteed _not_ to
/// compromise the kernel's memory safety.
///
/// # Memory Backing
///
/// A newly-created `VmSpace` is not backed by any physical memory pages. To
/// provide memory pages for a `VmSpace`, one can allocate and map physical
/// memory ([`UFrame`]s) to the `VmSpace` using the cursor.
///
/// A `VmSpace` can also attach a page fault handler, which will be invoked to
/// handle page faults generated from user space.
///
/// [`inject_post_schedule_handler`]: crate::task::inject_post_schedule_handler
/// [`UserMode::execute`]: crate::user::UserMode::execute
#[rustc_has_incoherent_inherent_impls]
pub struct VmSpace<'a> {
    pub pt: PageTable<UserPtConfig>,
    //    cpus: AtomicCpuSet,
    pub marker: PhantomData<&'a ()>,
}

/// A tracked struct for reasoning about verification-only properties of a [`VmSpace`].
#[rustc_has_incoherent_inherent_impls]
pub tracked struct VmSpaceOwner<'a> {
    /// Whether this VM space is currently active.
    pub active: bool,
    /// Active readers for this VM space.
    pub readers: Map<nat, VmIoOwner<'a>>,
    /// Active writers for this VM space.
    pub writers: Map<nat, VmIoOwner<'a>>,
}

impl<'a> Inv for VmSpaceOwner<'a> {
    open spec fn inv(self) -> bool {
        &&& self.readers.dom().finite()
        &&& self.writers.dom().finite()
        &&& self.active ==> {
            // Readers and writers are disjoint when the VM space is active.
            &&& self.readers.dom().disjoint(
                self.writers.dom(),
            )
            // Readers and writers are valid.
            &&& forall|i: nat, reader: VmIoOwner<'a>|
                #![trigger self.readers.kv_pairs().contains((i, reader))]
                self.readers.kv_pairs().contains((i, reader)) ==> reader.inv()
            &&& forall|i: nat, writer: VmIoOwner<'a>|
                #![trigger self.writers.kv_pairs().contains((i, writer))]
                self.writers.kv_pairs().contains((i, writer))
                    ==> writer.inv()
            // Readers do not overlap with other readers, and writers do not overlap with other writers.
            &&& forall|i, j: nat, reader: VmIoOwner<'a>, writer: VmIoOwner<'a>|
                #![trigger self.readers.kv_pairs().contains((i, reader)), self.writers.kv_pairs().contains((j, writer))]
                self.readers.kv_pairs().contains((i, reader)) && self.writers.kv_pairs().contains(
                    (j, writer),
                ) && i != j ==> !reader.overlaps(writer)
            &&& forall|i, j: nat, reader1: VmIoOwner<'a>, reader2: VmIoOwner<'a>|
                #![trigger self.readers.kv_pairs().contains((i, reader1)), self.readers.kv_pairs().contains((j, reader2))]
                self.readers.kv_pairs().contains((i, reader1)) && self.readers.kv_pairs().contains(
                    (j, reader2),
                ) && i != j ==> !reader1.overlaps(reader2)
            &&& forall|i, j: nat, writer1: VmIoOwner<'a>, writer2: VmIoOwner<'a>|
                #![trigger self.writers.kv_pairs().contains((i, writer1)), self.writers.kv_pairs().contains((j, writer2))]
                self.writers.kv_pairs().contains((i, writer1)) && self.writers.kv_pairs().contains(
                    (j, writer2),
                ) && i != j ==> !writer1.overlaps(writer2)
        }
    }
}

impl<'a> VmSpaceOwner<'a> {
    /// The basic invariant between a VM space and its owner.
    pub open spec fn inv_with(&self, vm_space: &VmSpace<'a>) -> bool {
        &&& self.inv()
    }
}

} // verus!
