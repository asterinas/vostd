// SPDX-License-Identifier: MPL-2.0
//! Demonstration of the linear-drop obligation mechanism.
//!
//! Concrete workbench showing what verification looks like when a
//! must-drop resource is honored vs. silently leaked. `clean_inv()` is the
//! boundary that breaks on leaks.
//!
//! After the per-frame migration there is a single must-drop ledger: the
//! per-instance `frame_obligations` multiset. Both `Frame<M>` and `Segment<M>`
//! use it.
//!
//! - `Frame<M>`: `ManuallyDrop::new(frame, ..)` mints one entry at
//!   `frame.key()` (paired with the recovery path); `Frame::drop` /
//!   `ManuallyDrop::new` redeem one.
//! - `Segment<M>`: records one entry per frame it holds (minted by
//!   [`crate::specs::mm::frame::segment::tracked_mint_seg_obligations`],
//!   drained on `Segment::drop`).
//!
//! Leaking either leaves `frame_obligations` non-empty, breaking the
//! `frame_obligations.len() == 0` conjunct of `clean_inv`.
//!
//! # How to use
//!
//! - As-shipped, [`demo_honored`] verifies.
//! - To see the leak case rejected, flip the `demo_leak` cfg gate on
//!   [`demo_leaked_when_enabled`] and re-run
//!   `cargo dv verify --targets ostd`. The expected error is documented in
//!   the comments above that function.
use vstd::prelude::*;

use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

verus! {

/// Honored: the obligation is minted on the per-frame ledger, then redeemed
/// before the function returns. Verifies cleanly.
#[verus_spec(
    with Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        old(regions).clean_inv(),
    ensures
        final(regions).clean_inv(),
)]
pub fn demo_honored(slot_idx: usize) {
    proof {
        let tracked obl = regions.tracked_mint_frame_obligation(slot_idx);
        // ... here a real caller would construct a Frame/Segment, hand it
        // around, etc. — for the demo we just immediately redeem.
        regions.tracked_redeem_frame_obligation(obl);
    }
}

// =============================================================================
// LEAK DEMO
// =============================================================================
//
// Body intentionally omits the `redeem` call. Gated behind the `demo_leak`
// cfg flag so the default build verifies — flip it on to reproduce the
// failure. The function promises `final(regions).clean_inv()` but the minted
// obligation never leaves `frame_obligations`, so the
// `frame_obligations.len() == 0` conjunct of `clean_inv` is unsatisfiable at
// function exit.
//
// Reproduce:
//
//     cargo dv verify --targets ostd \
//         -- --rustc-extra-args='--cfg demo_leak'
//
// or temporarily remove the `#[cfg(demo_leak)]` attribute below.
//
// Adding `regions.tracked_redeem_frame_obligation(obl)` at the end of the
// body (rebinding `_obl` → `obl`) makes verification succeed.
#[cfg(demo_leak)]
#[verus_spec(
    with Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        old(regions).clean_inv(),
    ensures
        final(regions).clean_inv(),
)]
pub fn demo_leaked_when_enabled(slot_idx: usize) {
    proof {
        // Mint a per-frame obligation — analog of `ManuallyDrop::new(frame, ..)`
        // or a single segment frame. No matching `Drop::drop` /
        // `ManuallyDrop::new` follows, so the multiset entry persists and
        // `clean_inv` fails on `frame_obligations.len() == 0` at function exit.
        let tracked _obl = regions.tracked_mint_frame_obligation(slot_idx);
    }
}

} // verus!
