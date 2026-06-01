// SPDX-License-Identifier: MPL-2.0
//! Demonstration of the linear-drop obligation mechanism.
//!
//! Concrete workbench showing what verification looks like when a
//! must-drop resource is honored vs. silently leaked. `clean_inv()` is the
//! boundary that breaks on leaks; today it covers two flavors of
//! must-drop:
//!
//! - `Segment<M>`: the per-instance ledger entry minted by
//!   `regions.tracked_mint_obligation(range)`. Leaking the token leaves
//!   `regions.obligations` non-empty.
//! - `Frame<M>`: the `raw_count` bumped by `ManuallyDrop::new(frame, ..)`.
//!   Leaking the forgotten frame leaves `slot_owners[idx].raw_count > 0`.
//!
//! # How to use
//!
//! - As-shipped, [`demo_honored`] verifies.
//! - To see either leak case rejected, flip the `demo_leak` cfg gate on
//!   the corresponding `demo_*_leaked_when_enabled` function and re-run
//!   `cargo dv verify --targets ostd`. The expected errors are documented
//!   in the comments above each gated function.

use core::ops::Range;
use vstd::prelude::*;
use vstd_extra::drop_tracking::DropObligation;

use crate::mm::Paddr;
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;

verus! {

/// Honored: the obligation is minted via the ledger, then redeemed before
/// the function returns. Verifies cleanly.
#[verus_spec(
    with Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        old(regions).clean_inv(),
        !old(regions).obligations.contains(range),
    ensures
        final(regions).clean_inv(),
)]
pub fn demo_honored(range: Range<Paddr>) {
    proof {
        let tracked obl = regions.tracked_mint_obligation(range);
        // ... here a real caller would construct a Segment, hand it
        // around, etc. — for the demo we just immediately redeem.
        regions.tracked_redeem_obligation(obl);
    }
}

// =============================================================================
// LEAK DEMO
// =============================================================================
//
// Body intentionally omits the `redeem` call. Gated behind the `demo_leak`
// cfg flag so the default build verifies — flip it on to reproduce the
// failure. The function promises `final(regions).clean_inv()` but the
// minted obligation never leaves `regions.obligations`, so the
// `obligations.is_empty()` conjunct of `clean_inv` is unsatisfiable at
// function exit.
//
// Reproduce:
//
//     cargo dv verify --targets ostd \
//         -- --rustc-extra-args='--cfg demo_leak'
//
// or temporarily remove the `#[cfg(demo_leak)]` attribute below.
//
// Verifier output (captured 2026-06-01):
//
//     error: postcondition not satisfied
//       --> ostd/src/mm/frame/obligation_demo.rs:NN:9
//        |
//     NN |         final(regions).clean_inv(),
//        |         ^^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition
//     ...
//        |  ___________-
//        | |         let tracked _obl = regions.tracked_mint_obligation(range);
//     ...|
//        | |_____- at the end of the function body
//
//     note: diagnostics via expansion
//        --> ostd/specs/mm/frame/meta_region_owners.rs:NN:13
//         |
//      NN |         &&& self.obligations.is_empty()
//         |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^
//
//     note:
//     (mut_ref_future(old(regions))).clean_inv()
//     |   (mut_ref_future(old(regions))).inv() ✔
//     |   (mut_ref_future(old(regions))).obligations.is_empty() ✘
//     |   |   (mut_ref_future(old(regions))).obligations =~= empty()
//     |   |       datatype is opaque here
//     |   +---
//     +---
//
// Adding `regions.tracked_redeem_obligation(obl)` at the end of the body
// (rebinding `_obl` → `obl`) makes verification succeed.
#[cfg(demo_leak)]
#[verus_spec(
    with Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        old(regions).clean_inv(),
        !old(regions).obligations.contains(range),
    ensures
        final(regions).clean_inv(),
)]
pub fn demo_leaked_when_enabled(range: Range<Paddr>) {
    proof {
        let tracked _obl = regions.tracked_mint_obligation(range);
        // No redeem! The ledger ends with `range` outstanding, breaking
        // `clean_inv()` at function exit.
    }
}

// =============================================================================
// FRAME LEAK DEMO
// =============================================================================
//
// Same idea, different mechanism. `ManuallyDrop::new(frame, ..)` bumps
// `slot_owners[idx].raw_count` (Frame's `TrackDrop::constructor_spec`). The
// matching recovery is `Frame::from_raw(paddr)`, which decrements it back
// to zero. Skipping the recovery — i.e. silently dropping the
// `ManuallyDrop<Frame<M>>` without `from_raw`-ing — leaves `raw_count` at
// `1`. With `clean_inv` now requiring `raw_count == 0` universally, the
// boundary check fails.
//
// This demo mutates `raw_count` directly (no real Frame plumbing) so we
// don't need to construct a full `Frame<M>` instance. The verifier still
// shows the failure attributable to the `raw_count == 0` conjunct.
//
// Reproduce by flipping the `#[cfg(demo_leak)]` gate.
//
// The Frame leak demo uses the per-Frame ledger directly:
// `tracked_mint_frame_obligation` adds an entry to
// `frame_obligations`, and skipping the matching redeem leaves it
// non-empty. `clean_inv` fails on the `frame_obligations.len() == 0`
// conjunct.
#[cfg(demo_leak)]
#[verus_spec(
    with Tracked(regions): Tracked<&mut MetaRegionOwners>
    requires
        old(regions).clean_inv(),
    ensures
        final(regions).clean_inv(),
)]
pub fn demo_frame_leaked_when_enabled(slot_idx: usize) {
    proof {
        // Mint a Frame obligation — analog of `ManuallyDrop::new(frame, ..)`.
        // No matching `Drop::drop` or `ConsumeDrop::new` follows, so the
        // multiset entry persists and `clean_inv` fails at function exit.
        let tracked _obl = regions.tracked_mint_frame_obligation(slot_idx);
    }
}

} // verus!
