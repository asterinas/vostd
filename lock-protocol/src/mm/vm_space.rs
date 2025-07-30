// SPDX-License-Identifier: MPL-2.0
//! Virtual memory space management.
//!
//! The [`VmSpace`] struct is provided to manage the virtual memory space of a
//! user. Cursors are used to traverse and modify over the virtual memory space
//! concurrently. The VM space cursor [`self::Cursor`] is just a wrapper over
//! the page table cursor [`super::page_table::Cursor`], providing efficient,
//! powerful concurrent accesses to the page table, and suffers from the same
//! validity concerns as described in [`super::page_table::cursor`].
use core::{ops::Range, sync::atomic::Ordering};
use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::pow2;
use vstd::prelude::*;
use vstd::bits::*;

use crate::mm::page_table::{PageTableConfig, PagingConsts};
use crate::mm::frame::Frame;
use crate::mm::page_prop::PageProperty;
use crate::mm::{PagingLevel, Paddr};
use crate::exec::MockPageTableEntry;

verus! {

use vstd::prelude::verus;
use super::allocator::AllocatorModel;
use super::meta::AnyFrameMeta;
use super::PAGE_SIZE;

// TODO: VmSpace
// TODO: Cursor
// TODO: CursorMut
// TODO: cpu_local_cell!
// TODO: VmItem
/// A token that can be used to mark a slot in the VM space.
///
/// The token can be converted to and from a [`usize`] value. Available tokens
/// are non-zero and capped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token(usize);

impl Token {
    /// The mask that marks the available bits in a token.
    // const MASK: usize = ((1 << 39) - 1) / PAGE_SIZE;
    #[verifier::allow_in_spec]
    pub fn MASK() -> usize
        returns
            0x7FFFFFF as usize,
    {
        assert(((1usize << 39) - 1) / PAGE_SIZE() as int == 0x7FFFFFF as usize) by (compute_only);
        ((1usize << 39) - 1) / PAGE_SIZE()
    }

    pub(crate) fn into_raw_inner(self) -> usize {
        self.0
    }

    /// Creates a new token from a raw value.
    ///
    /// # Safety
    ///
    /// The raw value must be a valid token created by [`Self::into_raw_inner`].
    pub(crate) fn from_raw_inner(raw: usize) -> Self
    // requires
    //     raw & !Self::MASK_SPEC() == 0, // TODO
     {
        Self(raw)
    }
}

impl TryFrom<usize> for Token {
    type Error = ();

    fn try_from(value: usize) -> core::result::Result<Self, Self::Error>
        requires
            0 <= value && value < Self::MASK(),
    {
        if value & Self::MASK() == 0 || value != 0 {
            Ok(Self(value * PAGE_SIZE()))
        } else {
            Err(())
        }
    }
}

impl From<Token> for usize {
    fn from(token: Token) -> usize {
        token.0 / PAGE_SIZE()
    }
}

/// A status that can be used to mark a slot in the VM space.
///
/// The status can be converted to and from a [`usize`] value. Available status
/// are non-zero and capped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Status(pub usize);

impl Status {
    /// The mask that marks the available bits in a status.
    const MASK: usize = 0x7ffffff;

    #[verifier::allow_in_spec]
    pub fn into_raw_inner(self) -> usize
        returns
            self.0,
    {
        // debug_assert!(self.0 & !Self::MASK == 0);
        // debug_assert!(self.0 != 0);
        self.0
    }

    /// Creates a new status from a raw value.
    ///
    /// # Safety
    ///
    /// The raw value must be a valid status created by [`Self::into_raw_inner`].
    #[verifier::allow_in_spec]
    pub unsafe fn from_raw_inner(raw: usize) -> Self
        returns
            Self(raw),
    {
        // debug_assert!(raw & !Self::MASK == 0);
        // debug_assert!(raw != 0);
        Self(raw)
    }
}

impl TryFrom<usize> for Status {
    type Error = ();

    fn try_from(value: usize) -> core::result::Result<Self, Self::Error> {
        if (value & !Self::MASK == 0) && value != 0 {
            assume(value * PAGE_SIZE() < usize::MAX);  // This should be trivial
            Ok(Self(value * PAGE_SIZE()))
        } else {
            Err(())
        }
    }
}

impl From<Status> for usize {
    fn from(status: Status) -> usize {
        status.0 / PAGE_SIZE()
    }
}

pub struct UntypedFrameMeta;

impl AnyFrameMeta for UntypedFrameMeta {

}

/// The item that can be mapped into the [`VmSpace`].
pub enum VmItem {
    /// Actually mapped a physical frame into the VM space.
    Frame(Frame<UntypedFrameMeta>, PageProperty),
    /// Marked with a [`Status`], without actually mapping a physical frame.
    Status(Status, PagingLevel),
}

// #[derive(Clone, Debug)]
pub(crate) struct UserPtConfig {}

// SAFETY: `item_into_raw` and `item_from_raw` are implemented correctly,
unsafe impl PageTableConfig for UserPtConfig {
    fn TOP_LEVEL_INDEX_RANGE() -> Range<usize> {
        0..256
    }

    open spec fn TOP_LEVEL_INDEX_RANGE_spec() -> Range<usize> {
        0..256
    }

    fn TOP_LEVEL_CAN_UNMAP() -> bool {
        true
    }

    open spec fn TOP_LEVEL_CAN_UNMAP_spec() -> bool {
        true
    }

    type E = MockPageTableEntry;

    type C = PagingConsts;

    type Item = VmItem;

    fn item_into_raw(item: Self::Item) -> (res: (Paddr, PagingLevel, PageProperty))
        ensures
            res == Self::item_into_raw_spec(item),
    {
        match item {
            VmItem::Frame(frame, prop) => {
                let level = frame.map_level();
                let paddr = frame.into_raw();
                (paddr, level, prop)
            },
            VmItem::Status(status, level) => {
                let raw_inner = status.into_raw_inner();
                (raw_inner as Paddr, level, PageProperty::new_absent())
            },
        }
    }

    open spec fn item_into_raw_spec(item: Self::Item) -> (Paddr, PagingLevel, PageProperty) {
        match item {
            VmItem::Frame(frame, prop) => {
                let level = frame.map_level();
                let paddr = frame.start_paddr();
                (paddr, level, prop)
            },
            VmItem::Status(status, level) => {
                let raw_inner = status.into_raw_inner();
                (raw_inner as Paddr, level, PageProperty::new_absent())
            },
        }
    }

    unsafe fn item_from_raw(
        paddr: Paddr,
        level: PagingLevel,
        prop: PageProperty,
        Tracked(alloc_model): Tracked<&AllocatorModel<crate::mm::vm_space::UntypedFrameMeta>>,
    ) -> Self::Item {
        if prop.has_map {
            // debug_assert_eq!(level, 1);
            // SAFETY: The caller ensures safety.
            assume(alloc_model.meta_map.contains_key(paddr as int));  // TODO: We need a from_raw -> into_raw model to prove this
            let frame = unsafe { Frame::from_raw(paddr, Tracked(alloc_model)) };
            VmItem::Frame(frame, prop)
        } else {
            // SAFETY: The caller ensures safety.
            let status = unsafe { Status::from_raw_inner(paddr) };
            VmItem::Status(status, level)
        }
    }
}

// TODO: TryFrom<PageTableItem> for VmItem
} // verus!
