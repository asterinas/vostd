//! **Proof-of-concept region owning the refcount TSM's per-slot bundles.**
//!
//! We are planning to transition
//! [`MetaRegionOwners`](crate::specs::mm::frame::meta_region_owners::MetaRegionOwners) to separate
//! out the shared `ref_count` permission, which the `rc_tsm` needs anyway.
//! This is a local stand-in for that future `MetaRegionOwners`.
//!
//! It is deliberately shaped like the real one (with some fields omitted),
//! so the migration is a substitution rather than a redesign:
//!
//! | `MetaRegionOwners`         | `TmpRegionOwners`                 |
//! |----------------------------|-----------------------------------|
//! | `slots`                    | same, unchanged                   |
//! | `slot_owners` (rc part)    | `rc_slots: Map<int, FrameRcSlot>` |
//! | `slot_owners` (remainder)  | omitted (add when finalized)      |
//! | `frame_obligations         | omitted (will be deleted)         |
//!
//! and the invariant mirrors the real one clause for clause: indexed by
//! [`max_meta_slots`], `slots ⊇ rc_slots`, `slots[i].is_init()`,
//! `slots[i].addr() == index_to_meta(i)`. Where the real region says
//! `slots[i].value().wf(slot_owners[i])`, this says
//! `rc_slots[i].wf(slots[i].value().ref_count.id(), i)` — the bundle governs the
//! cell that slot's own value names.
//!
//! # No storage permission
//!
//! The planned split separates **only** `ref_count`; `storage` stays inside
//! `MetaSlotOwner.inner_perms`, threaded by `&mut` as today. So there is no
//! storage permission for this region to take custody of, and the machine is
//! instantiated at [`NoStorage`] — its `storage` field carries `()`.
//! That is probably a sign that it should be removed from `rc_tsm` as well,
//! as it will be handled by the fractional permissions instead.
//!
//! # What this establishes
//!
//! The ops are reachable from **production-shaped inputs** — see
//! [`tsm_acquire_frame`], which takes a `Paddr` and this region, computes the
//! metadata address the way `meta.rs` does, and drives the CAS on the
//! resulting `MetaSlot`'s actual `ref_count` cell. When the `MetaRegionOwners`
//! structure is stable, we will be able to port to it and keep expanding.
//!
//! This is a temporary module: **delete it once the real `MetaRegionOwners` owns
//! the bundles.**
use vstd::atomic::*;
use vstd::map::group_map_lemmas;
use vstd::map::*;
use vstd::prelude::*;
use vstd::simple_pptr::{self, PPtr};
use vstd_extra::ownership::Inv;

use crate::specs::mm::frame::mapping::{frame_to_index, index_to_meta, max_meta_slots};
use super::rc_tsm::*;
use crate::mm::frame::meta::{MetaSlot, mapping::frame_to_meta};
use crate::mm::{Paddr, Vaddr};
use crate::specs::arch::{PAGE_SIZE, valid_frame_paddr};

verus! {

/// The machine's storage type in this PoC. The planned split hands over only the
/// `ref_count` permission, so there is no storage permission to park — see the
/// module docs for what that costs.
pub type NoStorage = ();

/// The future `MetaRegionOwners`, with the `ref_count` half split out into
/// per-slot TSM bundles.
///
/// `slots` is carried verbatim from the real region — which is what lets the
/// invariant *derive* each bundle's cell from the slot's own value, instead of
/// tracking cell identity separately.
pub tracked struct TmpRegionOwners {
    pub slots: Map<int, &'static simple_pptr::PointsTo<MetaSlot>>,
    pub rc_slots: Map<int, FrameRcSlot<NoStorage>>,
}

impl Inv for TmpRegionOwners {
    /// Mirrors [`MetaRegionOwners::inv`] clause for clause, with
    /// `slots[i].value().wf(slot_owners[i])` replaced by the TSM's version:
    /// slot `i`'s bundle governs slot `i`'s own `ref_count` cell, in namespace
    /// `i` — the per-slot namespace discipline (Phase 0) at region scale.
    open spec fn inv(self) -> bool {
        &&& {
            forall|i: int| 0 <= i < max_meta_slots() <==> #[trigger] self.rc_slots.contains_key(i)
        }
        &&& { forall|i: int| #[trigger] self.rc_slots.contains_key(i) ==> self.slots.contains_key(i) }
        &&& { forall|i: int| #[trigger] self.slots.contains_key(i) ==> 0 <= i < max_meta_slots() }
        &&& {
            forall|i: int| #[trigger]
                self.slots.contains_key(i) ==> {
                    &&& self.slots[i].is_init()
                    &&& self.slots[i].addr() == index_to_meta(i)
                    &&& self.rc_slots[i].wf(self.slots[i].value().ref_count.id(), i)
                }
        }
    }
}

/// Build the per-slot bundles for `[0, n)` — the recursive core of the custody
/// handover.
///
/// Note there is **no axiom here**: this is a plain recursive proof fn over
/// [`tracked_bind_slot`]. Region-scale binding costs nothing extra in
/// soundness — only the recursion.
pub proof fn tracked_bind_rc_slots(tracked rc_perms: Map<int, PermissionU64>, n: nat) -> (tracked
    res: Map<int, FrameRcSlot<NoStorage>>)
    requires
        forall|i: int| 0 <= i < n ==> #[trigger] rc_perms.contains_key(i),
        forall|i: int| 0 <= i < n ==> (#[trigger] rc_perms[i]).value() == REF_COUNT_UNUSED,
        n <= usize::MAX,
    ensures
        forall|i: int| 0 <= i < n <==> #[trigger] res.contains_key(i),
        forall|i: int| 0 <= i < n ==> (#[trigger] res[i]).wf(rc_perms[i].id(), i),
    decreases n,
{
    broadcast use group_map_lemmas;

    let tracked mut rcp = rc_perms;

    if n == 0 {
        Map::tracked_empty()
    } else {
        let ghost last = n - 1;

        // Peel off the top slot, bind everything below it, then add it back.
        let tracked rc_perm = rcp.tracked_remove(last);
        let ghost rc1 = rcp;

        let tracked mut bundles = tracked_bind_rc_slots(rcp, (n - 1) as nat);
        let ghost bundles0 = bundles;
        let tracked no_storage: NoStorage = ();
        let tracked bundle = tracked_bind_slot(rc_perm, no_storage, last as usize);

        bundles.tracked_insert(last, bundle);

        // Bridge the recursive result back to the *entry* map: removing `last`
        // left every lower key untouched, and inserting `last` leaves them
        // untouched again.
        assert forall|i: int| 0 <= i < n implies (#[trigger] bundles[i]).wf(rc_perms[i].id(), i) by {
            if i < last {
                assert(bundles0[i].wf(rc1[i].id(), i));
                assert(rc1[i] == rc_perms[i]);
            }
        }
        bundles
    }
}

/// **The custody handover.** Take the region's slot pointers plus the split-out
/// `ref_count` permissions, and return a region in which those cells are
/// TSM-governed.
///
/// Each slot's machine is created in the `Unused` band, which is why every cell
/// must read [`REF_COUNT_UNUSED`] going in; that is exactly the state
/// `alloc_meta_frames` leaves the whole region in at initialization.
///
/// `rc_perms[i].is_for(slots[i].value().ref_count)` is the input form of what
/// becomes the invariant's derived-cell clause: the permission handed over for
/// slot `i` must be the permission for *that slot's* cell.
pub proof fn tracked_bind_all(
    tracked slots: Map<int, &'static simple_pptr::PointsTo<MetaSlot>>,
    tracked rc_perms: Map<int, PermissionU64>,
) -> (tracked res: TmpRegionOwners)
    requires
        max_meta_slots() <= usize::MAX,
        forall|i: int| 0 <= i < max_meta_slots() <==> #[trigger] slots.contains_key(i),
        forall|i: int| 0 <= i < max_meta_slots() ==> #[trigger] rc_perms.contains_key(i),
        forall|i: int| #[trigger]
            slots.contains_key(i) ==> {
                &&& slots[i].is_init()
                &&& slots[i].addr() == index_to_meta(i)
            },
        forall|i: int| 0 <= i < max_meta_slots() ==> (#[trigger] rc_perms[i]).value()
            == REF_COUNT_UNUSED,
        forall|i: int| 0 <= i < max_meta_slots() ==> (#[trigger] rc_perms[i]).is_for(
            slots[i].value().ref_count,
        ),
    ensures
        res.inv(),
{
    let tracked bundles = tracked_bind_rc_slots(rc_perms, max_meta_slots() as nat);
    TmpRegionOwners { slots, rc_slots: bundles }
}

/// Hand out an **owned** governing bundle for slot `idx`.
///
/// This is the piece a real handle needs. `Frame<M>` is an owned value that
/// outlives any borrow of the region, so it cannot carry `&FrameRcSlot`; it
/// needs its own copy of the right to open that slot's cell. Because the
/// invariant lives in a [`Shared`](vstd::shared::Shared) and the machine
/// `Instance` is duplicable, [`FrameRcSlot::share`] produces exactly that, and
/// the result borrows nothing from the region.
///
/// This is duplication of *access*, not of *authority*: the returned bundle
/// still opens nothing without a `reader` / `permit` / `unique` token, and those
/// remain linear. Every handle may look; only a token holder may act.
pub proof fn tracked_slot_handle(tracked region: &TmpRegionOwners, idx: int) -> (tracked res:
    FrameRcSlot<NoStorage>)
    requires
        region.inv(),
        0 <= idx < max_meta_slots(),
    ensures
        res.wf(region.slots[idx].value().ref_count.id(), idx),
{
    assert(region.rc_slots.contains_key(idx));
    let tracked rc = region.rc_slots.tracked_borrow(idx);
    rc.share()
}

/// **The connection to real code.** Acquire the frame at `paddr`, reaching its
/// `MetaSlot` exactly the way `meta.rs` does.
///
/// Everything about the slot is real: `frame_to_meta(paddr)` computes the
/// metadata address, the `PointsTo<MetaSlot>` comes out of the region's own
/// `slots` map, and the CAS runs on that `MetaSlot`'s `ref_count` field. This
/// takes the same shape as `get_from_unused(paddr)` — one region, one physical
/// address — because the region now carries the slot pointers itself.
pub fn tsm_acquire_frame(paddr: Paddr, Tracked(region): Tracked<&TmpRegionOwners>) -> (res: Option<
    Tracked<FrameRc::reader<NoStorage>>,
>)
    requires
        region.inv(),
        valid_frame_paddr(paddr),
        0 <= frame_to_index(paddr) < max_meta_slots(),
{
    let ghost idx = frame_to_index(paddr);
    assert(region.rc_slots.contains_key(idx));
    let tracked slot_perm = region.slots.tracked_borrow(idx);

    let vaddr: Vaddr = frame_to_meta(paddr);
    // SAFETY: mirrors `inc_frame_ref_count` — `vaddr` names a valid `MetaSlot`
    // that is never mutably borrowed, so an immutable reference is safe.
    let slot = PPtr::<MetaSlot>::from_addr(vaddr).borrow(Tracked(slot_perm));

    let idx_exec: usize = paddr / PAGE_SIZE;
    tsm_region_acquire(slot, idx_exec, Tracked(region))
}

/// Acquire a free slot through the region: borrow its bundle, CAS
/// `REF_COUNT_UNUSED → 0`, then publish at `1`.
///
/// This is `get_from_unused` in miniature — the caller starts with **no token at
/// all**, names a slot by index, and comes back holding a linear reader token.
/// Between the two atomics the cell physically reads `0` and this caller
/// provably owns the window, because it holds the only permit.
pub fn tsm_region_acquire(
    slot: &MetaSlot,
    idx: usize,
    Tracked(region): Tracked<&TmpRegionOwners>,
) -> (res: Option<Tracked<FrameRc::reader<NoStorage>>>)
    requires
        region.inv(),
        0 <= idx < max_meta_slots(),
        *slot == region.slots[idx as int].value(),
{
    assert(region.rc_slots.contains_key(idx as int));
    let tracked rc = region.rc_slots.tracked_borrow(idx as int);

    if let Some(pair) = tsm_try_claim::<NoStorage>(slot, idx, Tracked(rc)) {
        let tracked perm = pair.0.get();
        let tracked permit = pair.1.get();
        // `write_meta(metadata)` would happen here, under the permit.
        Some(tsm_publish_shared::<NoStorage>(slot, idx, Tracked(rc), Tracked(permit), Tracked(perm)))
    } else {
        None
    }
}

/// Acquire a free slot and walk away with a self-contained handle: the reader
/// token **plus** its own governing bundle, neither of which borrows the region.
///
/// This is the shape a real `Frame<M>` would have.
pub fn tsm_region_acquire_owned(
    slot: &MetaSlot,
    idx: usize,
    Tracked(region): Tracked<&TmpRegionOwners>,
) -> (res: Option<(Tracked<FrameRcSlot<NoStorage>>, Tracked<FrameRc::reader<NoStorage>>)>)
    requires
        region.inv(),
        0 <= idx < max_meta_slots(),
        *slot == region.slots[idx as int].value(),
{
    let tracked owned = tracked_slot_handle(region, idx as int);

    // From here on the region is not consulted: the op runs off the owned bundle.
    if let Some(r) = tsm_region_acquire_with(slot, idx, Tracked(&owned)) {
        Some((Tracked(owned), r))
    } else {
        None
    }
}

/// The acquire sequence, driven by a bundle the caller already owns.
pub fn tsm_region_acquire_with(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<NoStorage>>,
) -> (res: Option<Tracked<FrameRc::reader<NoStorage>>>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
{
    if let Some(pair) = tsm_try_claim::<NoStorage>(slot, idx, Tracked(rc)) {
        let tracked perm = pair.0.get();
        let tracked permit = pair.1.get();
        Some(tsm_publish_shared::<NoStorage>(slot, idx, Tracked(rc), Tracked(permit), Tracked(perm)))
    } else {
        None
    }
}

/// Release a handle through the region: `fetch_sub`, and if it was the last
/// reference, run the teardown window to completion and hand the slot back to
/// the free pool.
///
/// `Frame::drop` in miniature. The `if` here is not a check the caller could get
/// wrong — `dec_to_zero` is what *produces* the permit, so the teardown branch is
/// reachable only when this really was the last reference.
pub fn tsm_region_release(
    slot: &MetaSlot,
    idx: usize,
    Tracked(region): Tracked<&TmpRegionOwners>,
    Tracked(reader): Tracked<FrameRc::reader<NoStorage>>,
)
    requires
        region.inv(),
        0 <= idx < max_meta_slots(),
        *slot == region.slots[idx as int].value(),
        reader.instance_id() == region.rc_slots[idx as int].inst.id(),
{
    assert(region.rc_slots.contains_key(idx as int));
    let tracked rc = region.rc_slots.tracked_borrow(idx as int);

    if let Some(pair) = tsm_dec_ref_count::<NoStorage>(slot, idx, Tracked(rc), Tracked(reader)) {
        let tracked perm = pair.0.get();
        let tracked permit = pair.1.get();
        // `drop_meta_in_place()` would happen here, under the permit.
        tsm_recycle::<NoStorage>(slot, idx, Tracked(rc), Tracked(permit), Tracked(perm));
    }
}

} // verus!
