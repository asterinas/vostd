// SPDX-License-Identifier: MPL-2.0
//! Implementation of the free heap slot list.
use vstd::prelude::*;

use core::ptr::NonNull;

use super::HeapSlot;

verus! {

pub assume_specification<T>[ <*mut T>::write ](ptr: *mut T, val: T);

pub assume_specification<T>[ <*mut T>::read ](ptr: *mut T) -> T;

pub assume_specification<T, U, F>[ core::option::Option::<T>::map_or ](_0: core::option::Option<T>, _1: U, _2: F) -> U
where
    F: core::ops::FnOnce(T,) -> U + core::marker::Destruct,
    U: core::marker::Destruct,
;

/// A singly-linked list of [`HeapSlot`]s from [`super::Slab`]s.
///
/// The slots inside this list will have a size of `SLOT_SIZE`. They can come
/// from different slabs.
#[derive(Debug)]
pub struct SlabSlotList<const SLOT_SIZE: usize> {
    /// The head of the list.
    head: Option<NonNull<u8>>,
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

impl<const SLOT_SIZE: usize> Default for SlabSlotList<SLOT_SIZE> {
    fn default() -> (res: Self)
        ensures
            res.is_empty_spec(),
    {
        Self::new()
    }
}

impl<const SLOT_SIZE: usize> SlabSlotList<SLOT_SIZE> {
    pub closed spec fn is_empty_spec(&self) -> bool {
        self.head is None
    }

    /// Creates a new empty list.
    pub const fn new() -> (res: Self)
        ensures
            res.is_empty_spec(),
    {
        Self { head: None }
    }

    /// Pushes a slot to the front of the list.
    ///
    /// # Panics
    ///
    /// Panics if
    ///  - the slot does not come from a slab
    ///    (i.e., `!matches(slot.info(), SlotInfo::SlabSlot(_))`);
    ///  - the size of the slot does not match `SLOT_SIZE`.
    pub fn push(&mut self, slot: HeapSlot) {
        let slot_ptr = slot.as_ptr();
        let super::SlotInfo::SlabSlot(slot_size) = slot.info() else {
            #[cfg(feature = "allow_panic")]
            panic!("The slot does not come from a slab");
            #[cfg(not(feature = "allow_panic"))]
             return;
        };

        #[cfg(feature = "allow_panic")]
        assert_eq!(slot_size, SLOT_SIZE);
        #[cfg(feature = "allow_panic")]
        const { assert!(SLOT_SIZE >= core::mem::size_of::<usize>()) };

        let original_head = self.head;

        #[cfg(feature = "allow_panic")]
        debug_assert!(!slot_ptr.is_null());
        // SAFETY: A pointer to a slot must not be NULL;
        self.head = Some(unsafe { NonNull::new_unchecked(slot_ptr) });
        // Write the original head to the slot.
        // SAFETY: A heap slot must be free so the pointer to the slot can be
        // written to. The slot size is at least the size of a pointer.
        unsafe {
            // slot_ptr.cast::<usize>().write(original_head.map_or(0, |h| h.as_ptr() as usize));
            slot_ptr.cast::<*mut u8>().write(original_head.map_or(core::ptr::null_mut(), |h| h.as_ptr()));
        }
    }

    /// Pops a slot from the front of the list.
    ///
    /// It returns `None` if the list is empty.
    // #[verifier::external_body]
    pub fn pop(&mut self) -> Option<HeapSlot> {
        let original_head = self.head?;

        // SAFETY: The head is a valid pointer to a free slot.
        // The slot contains a pointer to the next slot.
        // let next = unsafe { original_head.as_ptr().cast::<usize>().read() } as *mut u8;
        let next = unsafe { original_head.as_ptr().cast::<*mut u8>().read() };

        self.head = if next.is_null() {
            None
        } else {
            // SAFETY: We already verified that the next slot is not NULL.
            Some(unsafe { NonNull::new_unchecked(next) })
        };

        Some(unsafe { HeapSlot::new(original_head, super::SlotInfo::SlabSlot(SLOT_SIZE)) })
    }
}

} // verus!
