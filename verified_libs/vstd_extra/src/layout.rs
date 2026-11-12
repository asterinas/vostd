// SPDX-License-Identifier: MPL-2.0
//! Shared integer and atomic layouts, checked for the target during code generation.
use core::sync::atomic::AtomicU64;
use vstd::{
    layout::{align_of, size_of},
    prelude::*,
};

verus! {

global layout u16 is size == 2, align == 2;

global layout u32 is size == 4, align == 4;

global layout u64 is size == 8, align == 8;

global layout AtomicU64 is size == 8, align == 8;

/// Establishes the shared integer layouts.
pub proof fn lemma_primitive_layout()
    ensures
        size_of::<u16>() == 2,
        align_of::<u16>() == 2,
        size_of::<u32>() == 4,
        align_of::<u32>() == 4,
        size_of::<u64>() == 8,
        align_of::<u64>() == 8,
        core::mem::size_of::<u16>() == 2,
        core::mem::size_of::<u32>() == 4,
{
    broadcast use {VERUS_layout_of_u16, VERUS_layout_of_u32, VERUS_layout_of_u64};

}

/// Establishes the shared AtomicU64 layout.
pub proof fn lemma_atomic_u64_layout()
    ensures
        size_of::<AtomicU64>() == 8,
        align_of::<AtomicU64>() == 8,
{
    broadcast use VERUS_layout_of_AtomicU64;

}

} // verus!
