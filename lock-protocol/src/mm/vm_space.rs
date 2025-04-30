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

verus! {

use vstd::prelude::verus;
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
    pub open spec fn MASK_SPEC() -> (res: usize) {
        0x7FFFFFF
    }

    #[verifier::when_used_as_spec(MASK_SPEC)]
    pub fn MASK() -> (res: usize)
        ensures
            res == Self::MASK_SPEC(),
    {
        broadcast use lemma_u64_pow2_no_overflow;
        broadcast use lemma_u64_shl_is_mul;

        let t = ((1 as u64) << 39 as u64);
        assert(t == pow2(39 as nat)) by {
            lemma_u64_pow2_no_overflow(39 as nat);
            lemma_u64_shl_is_mul(1 as u64, 39 as u64);
        }
        reveal(pow2);
        reveal(pow);
        assert(pow2(39) == 0x8000000000) by (compute_only);
        assert(0 < t < u64::MAX) by {
            assert(pow2(39 as nat) == 0x8000000000) by (compute_only);
        }
        let res = ((t - 1) / PAGE_SIZE as u64) as usize;
        assert(res == 0x7FFFFFF) by {
            assert(res == (t - 1) as u64 / PAGE_SIZE as u64);
            assert(t - 1 == 0x8000000000 - 1);
            assert(PAGE_SIZE == 0x1000);
            assert(0x8000000000 - 1 == 0x7FFFFFFFFF) by (compute_only);
            assert(0x7FFFFFFFFF as usize / PAGE_SIZE == 0x7FFFFFF) by (compute_only);
        }
        res
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
            0 <= value && value < Self::MASK_SPEC(),
    {
        if value & Self::MASK() == 0 || value != 0 {
            Ok(Self(value * PAGE_SIZE))
        } else {
            Err(())
        }
    }
}

impl From<Token> for usize {
    fn from(token: Token) -> usize {
        token.0 / PAGE_SIZE
    }
}

// TODO: TryFrom<PageTableItem> for VmItem
} // verus!
