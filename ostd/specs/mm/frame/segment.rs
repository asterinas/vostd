// SPDX-License-Identifier: MPL-2.0
//! Spec/proof companion for [`crate::mm::frame::segment`].
use vstd::prelude::*;
use vstd_extra::drop_tracking::*;
use vstd_extra::ownership::*;

use core::ops::Range;

use crate::mm::frame::{AnyFrameMeta, MetaSlot, Segment, meta::META_SLOT_SIZE};
use crate::mm::{Paddr, Vaddr, paddr_to_vaddr};
use crate::specs::arch::{MAX_PADDR, PAGE_SIZE};
use crate::specs::mm::frame::mapping::{frame_to_index, meta_addr};
use crate::specs::mm::frame::meta_region_owners::MetaRegionOwners;
use crate::specs::mm::virt_mem::MemView;

verus! {

impl<M: AnyFrameMeta + ?Sized> TrackDrop for Segment<M> {
    /// The tracked state for `ManuallyDrop` purposes is the global
    /// [`MetaRegionOwners`]. The [`SegmentOwner<M>`] is threaded in
    /// separately via `verus_spec`, and the *real* per-segment obligation
    /// (with the segment-range ledger entry) is held on `SegmentOwner`
    /// itself — not via this `TrackDrop` impl. That keeps
    /// `ManuallyDrop::new(self, Tracked(regions))` callable in places like
    /// `Segment::split` / `Segment::into_raw` where the segment is
    /// "temporarily forgotten" without an actual ledger event.
    type State = MetaRegionOwners;

    /// Real segment-range key. The token produced by `constructor_spec`
    /// carries `self.range` as identity. The mint here does NOT insert
    /// into `obligations` — the real per-segment entry is added by
    /// [`Segment::from_unused`] and removed by [`Segment::drop`] directly.
    /// Carrying `Range<Paddr>` on the token still strengthens the
    /// discipline: a token forged for one segment can't masquerade as
    /// belonging to another (the `consume_requires`/`drop_requires`
    /// checks would refuse the mismatched key).
    type Key = Range<Paddr>;

    open spec fn key(self) -> Self::Key {
        self.range
    }

    open spec fn constructor_requires(self, s: Self::State) -> bool {
        true
    }

    open spec fn constructor_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl_key: Self::Key,
    ) -> bool {
        &&& s0 =~= s1
        &&& obl_key == self.range
    }

    proof fn constructor_spec(self, tracked s: &mut Self::State) -> (tracked obl: DropObligation<
        Self::Key,
    >) {
        DropObligation::tracked_mint(self.range)
    }

    open spec fn drop_requires(self, s: Self::State) -> bool {
        s.inv()
    }

    open spec fn drop_ensures(self, s0: Self::State, s1: Self::State, obl_key: Self::Key) -> bool {
        true
    }

    open spec fn consume_requires(self, s: Self::State, obl_key: Self::Key) -> bool {
        true
    }

    open spec fn consume_ensures(
        self,
        s0: Self::State,
        s1: Self::State,
        obl_key: Self::Key,
    ) -> bool {
        s0 =~= s1
    }

    proof fn consume_obligation(
        self,
        tracked s: &mut Self::State,
        tracked obl: DropObligation<Self::Key>,
    ) {
        // No-op: the token is ledger-less identity. The real segment-range
        // ledger lives on `SegmentOwner` and is redeemed by
        // `Segment::drop` directly, not via this hook.
    }
}

/// A [`SegmentOwner<M>`] holds the permission tokens for all frames in the
/// [`Segment<M>`] for verification purposes.
///
/// The `range` field tracks which physical-address range this owner corresponds
/// to. It is a ghost-only field used by [`Self::inv`] to express the structural
/// connection between `perms` and the segment's frames.
/// Number of frames in a page-aligned physical range.
#[verifier::inline]
pub open spec fn seg_nframes(range: Range<Paddr>) -> int {
    (range.end - range.start) / PAGE_SIZE as int
}

pub tracked struct SegmentOwner<M: AnyFrameMeta + ?Sized> {
    /// The physical-address range of the segment that this owner corresponds to.
    ///
    /// Design B (Arc-style): the owner no longer holds the per-frame slot
    /// permissions. Each frame's `simple_pptr::PointsTo<MetaSlot>` stays
    /// canonical in `regions.slots[idx]` and is *borrowed* on drop/next;
    /// the segment merely contributes one (forgotten) reference per frame.
    ///
    /// Per-frame linear-drop: the owner carries *no* obligation token. The
    /// segment's "must drop" guarantee is enforced entirely by the per-frame
    /// `regions.frame_obligations` multiset (one count per segment frame, see
    /// [`SegmentOwner::relate_regions`]) combined with the boundary
    /// `clean_inv()` check — silently dropping a `SegmentOwner` leaves those
    /// counts outstanding and breaks `clean_inv()`. Redeem-time tokens are
    /// fabricated on demand via `DropObligation::tracked_mint`, so no token
    /// needs to travel with the owner.
    pub ghost range: Range<Paddr>,
    pub _marker: core::marker::PhantomData<M>,
}

impl<M: AnyFrameMeta + ?Sized> Inv for SegmentOwner<M> {
    /// The invariant of a [`SegmentOwner`]:
    ///
    /// - the tracked `range` is page-aligned and within bounds;
    /// - the number of permissions matches the number of frames in the range;
    /// - each permission's address corresponds to the meta slot of its frame
    ///   (so consecutive permissions are spaced by `META_SLOT_SIZE`);
    /// - each permission is initialized and individually well-formed.
    /// - the bundled obligation token is keyed to this owner's `range`.
    open spec fn inv(self) -> bool {
        &&& self.range.start % PAGE_SIZE == 0
        &&& self.range.end % PAGE_SIZE == 0
        &&& self.range.start <= self.range.end <= MAX_PADDR
    }
}

impl<M: AnyFrameMeta + ?Sized> SegmentOwner<M> {
    /// The cross-object relation between a [`SegmentOwner`] and the global
    /// [`MetaRegionOwners`].
    ///
    /// For every frame `i` in the segment, this asserts:
    /// - the slot owner is present in `regions` and the perm matches it,
    /// - the slot's `slot_vaddr` is consistent with its index,
    /// - the slot has a live, non-`UNUSED` reference count,
    /// - `raw_count == 1` (the segment holds one forgotten reference per frame),
    /// - the slot's perm is *not* in `regions.slots` (it lives in `self.perms`),
    /// - distinct frames in the segment map to distinct slot indices.
    ///
    /// This is an invariant preserved by every operation that transforms a
    /// `SegmentOwner` together with `MetaRegionOwners` — analogous to
    /// [`crate::specs::mm::frame::unique::UniqueFrameOwner::global_inv`] but
    /// spanning all frames in a segment.
    pub open spec fn relate_regions(self, regions: MetaRegionOwners) -> bool {
        &&& forall|i: int|
            #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
            0 <= i < seg_nframes(self.range) ==> {
                let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                // Per-frame linear-drop: the segment holds one (forgotten)
                // reference per frame, recorded as a `frame_obligations` count.
                // Combined with the boundary `clean_inv()` (which requires the
                // multiset empty), this gates `Segment::drop`'s per-frame
                // redeem against a genuine outstanding entry — the per-frame
                // analogue of the old `obligations.contains(range)` check.
                &&& regions.frame_obligations.count(idx) >= 1
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots.contains_key(
                    idx,
                )
                // Borrow-protocol transition: `raw_count` is dormant.
                &&& regions.slot_owners[idx].slot_vaddr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    > 0
                // Segment frames are shared (never `UNIQUE`); the upper
                // bound also keeps post-`fetch_sub` out of the forbidden
                // `(REF_COUNT_MAX, REF_COUNT_UNIQUE)` zone.
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                // A segment holds its frames as a unit; they are not
                // mapped into any page table, so the slot carries no PTE
                // paths. Needed to discharge `Frame::drop`'s strengthened
                // precondition (`ref_count == 1 ==> paths_in_pt empty`)
                // in the per-frame teardown loop.
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage is Frame
            }
        &&& forall|i: int, j: int|
            #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize),
                frame_to_index((self.range.start + j * PAGE_SIZE) as usize)]
            0 <= i < j < seg_nframes(self.range) ==> frame_to_index(
                (self.range.start + i * PAGE_SIZE) as usize,
            ) != frame_to_index((self.range.start + j * PAGE_SIZE) as usize)
    }

    /// Manually instantiates the [`relate_regions`] forall at a specific index.
    /// Use this to extract per-frame facts (slot_owner present, slot perm in
    /// `regions.slots`, raw_count == 1, ref_count > 0, etc.) without fighting
    /// trigger inference.
    pub proof fn relate_regions_at(self, regions: MetaRegionOwners, i: int)
        requires
            self.relate_regions(regions),
            0 <= i < seg_nframes(self.range),
        ensures
            ({
                let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                &&& regions.frame_obligations.count(idx) >= 1
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots.contains_key(
                    idx,
                )
                // Borrow-protocol transition: `raw_count` is dormant.
                &&& regions.slot_owners[idx].slot_vaddr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value() > 0
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    <= crate::mm::frame::meta::REF_COUNT_MAX
                &&& regions.slot_owners[idx].paths_in_pt.is_empty()
                &&& regions.slot_owners[idx].usage is Frame
            }),
    {
        // Trigger the forall at index `i`.
        let _ = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
    }

    /// Manually instantiates the [`relate_regions`] distinctness forall at a
    /// specific index pair: distinct in-range frames map to distinct slot
    /// indices. Reusable lever for `from_unused`/`split`/`slice` proofs.
    pub proof fn relate_regions_distinct(self, regions: MetaRegionOwners, i: int, j: int)
        requires
            self.relate_regions(regions),
            0 <= i < j < seg_nframes(self.range),
        ensures
            frame_to_index((self.range.start + i * PAGE_SIZE) as usize) != frame_to_index(
                (self.range.start + j * PAGE_SIZE) as usize,
            ),
    {
        // Trigger the distinctness forall at `(i, j)`.
        let _ = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
        let _ = frame_to_index((self.range.start + j * PAGE_SIZE) as usize);
    }
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// The well-formedness relation between a [`Segment`] and its owner:
    ///
    /// - the segment's range matches the range tracked by the owner;
    /// - the number of permissions in the owner matches the number of frames in the segment;
    /// - the physical address of each permission matches the corresponding frame in the segment.
    ///
    /// This is *only* the cross-object relation; callers are expected to also
    /// state `self.inv()` (and where relevant `owner.inv()`) alongside. With
    /// `owner.inv()` the perm-address and length conjuncts are consequences of
    /// `self.range == owner.range`, but they are kept here for trigger
    /// availability at sites that don't invoke `owner.inv()`.
    ///
    /// Interested readers are encouraged to see [`frame_to_index`] and [`meta_addr`] for how
    /// we convert between physical addresses and meta region indices.
    pub open spec fn wf(&self, owner: &SegmentOwner<M>) -> bool {
        &&& self.range == owner.range
    }

    /// The bundled invariant for [`Segment`] operations that thread an `owner`
    /// and the global `regions`: the segment's own invariant, its
    /// well-formedness against the owner, the owner's invariant, the region
    /// invariant, and the cross-object relation tying the owner to `regions`.
    ///
    /// Mirrors the `invariants` bundles used throughout the page-table / cursor
    /// code — it collapses the five clauses repeated verbatim across `split`,
    /// `slice`, `into_raw`, `next`, and `drop` into one predicate.
    pub open spec fn invariants(&self, owner: &SegmentOwner<M>, regions: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& self.wf(owner)
        &&& owner.inv()
        &&& regions.inv()
        &&& owner.relate_regions(regions)
    }

    /// Whether a [`MemView`] covers the segment through the kernel direct mapping.
    ///
    /// This predicate only describes the virtual-to-physical relation and the
    /// presence of initialized backing frame contents.
    pub open spec fn kernel_mem_view_covers(&self, view: &MemView) -> bool {
        &&& self.inv()
        &&& view.mappings_are_disjoint()
        &&& forall|vaddr: Vaddr|
            #![trigger view.addr_transl(vaddr)]
            paddr_to_vaddr(self.start_paddr()) <= vaddr < paddr_to_vaddr(self.start_paddr())
                + self.end_paddr() - self.start_paddr() ==> {
                &&& view.addr_transl(vaddr) is Some
                &&& view.memory.contains_key((view.addr_transl(vaddr)->0).0)
                &&& view.memory[(view.addr_transl(vaddr)->0).0].inv()
                &&& view.memory[(view.addr_transl(vaddr)->0).0].contents[(view.addr_transl(
                    vaddr,
                )->0).1 as int] is Init
            }
        &&& forall|paddr: Paddr|
            #![trigger paddr_to_vaddr(paddr)]
            self.start_paddr() <= paddr < self.end_paddr() ==> {
                let vaddr = paddr_to_vaddr(paddr);
                &&& view.addr_transl(vaddr) is Some
                &&& (view.addr_transl(vaddr)->0).0 <= paddr
                &&& paddr < (view.addr_transl(vaddr)->0).0 + view.memory[(view.addr_transl(
                    vaddr,
                )->0).0].size@
                &&& (view.addr_transl(vaddr)->0).1 == paddr - (view.addr_transl(vaddr)->0).0
                &&& view.memory.contains_key((view.addr_transl(vaddr)->0).0)
                &&& view.memory[(view.addr_transl(vaddr)->0).0].inv()
                &&& view.memory[(view.addr_transl(vaddr)->0).0].contents[(view.addr_transl(
                    vaddr,
                )->0).1 as int] is Init
            }
    }
}

/// Helper spec: the slot index of the j-th frame in a segment whose physical
/// range starts at `range_start`. Unlike a let-bound ghost closure (which Verus
/// treats opaquely under SMT), a `spec fn` is auto-unfolded so equalities
/// between `frame_idx_at(...)` and `frame_to_index(...)` are derivable.
#[verifier::inline]
pub open spec fn frame_idx_at(range_start: usize, j: int) -> usize {
    frame_to_index((range_start + j * PAGE_SIZE) as usize)
}

/// The exact `frame_obligations` effect of recording one forgotten reference
/// per frame for the first `n` frames of a segment starting at `range_start`:
///
/// - every segment frame's count grows by at least one (its recorded
///   reference), and
/// - the *frame condition*: every slot that is NOT a segment frame is left
///   untouched.
///
/// The frame condition is the load-bearing part — it pins the *support* of the
/// change to the segment's slots, so a caller's ledger accounting telescopes
/// (it can conclude this only touched the segment's slots). Shared by
/// [`tracked_mint_seg_obligations`] (which establishes it) and
/// [`Segment::from_unused`] (which advertises it).
pub open spec fn seg_obligations_minted(
    pre: MetaRegionOwners,
    post: MetaRegionOwners,
    range_start: usize,
    n: int,
) -> bool {
    // Each segment frame gains at least one entry.
    &&& forall|i: int|
        #![trigger frame_to_index((range_start + i * PAGE_SIZE) as usize)]
        0 <= i < n ==> post.frame_obligations.count(
            frame_to_index((range_start + i * PAGE_SIZE) as usize),
        ) >= pre.frame_obligations.count(frame_to_index((range_start + i * PAGE_SIZE) as usize))
            + 1
        // Frame condition: every slot that is NOT a segment frame is untouched.
    &&& forall|jdx: usize|
        #![trigger post.frame_obligations.count(jdx)]
        (forall|i: int|
            #![trigger frame_to_index((range_start + i * PAGE_SIZE) as usize)]
            0 <= i < n ==> jdx != frame_to_index((range_start + i * PAGE_SIZE) as usize))
            ==> post.frame_obligations.count(jdx) == pre.frame_obligations.count(jdx)
}

/// Mints one per-frame `frame_obligations` entry for each of the first `n`
/// frames of a segment starting at `range_start`. Used by
/// [`Segment::from_unused`] to record the segment's forgotten per-frame
/// references *after* the construction loop (which is net-zero on the ledger:
/// each frame's `Frame::from_unused` mint is cancelled by its `ManuallyDrop`).
///
/// Per-frame obligations replace the old single range-keyed `obligations`
/// ledger entry. Because `frame_obligations` is a multiset and minting only
/// ever increases counts, no distinctness hypothesis on the frame indices is
/// needed.
///
/// EXACT accounting (Tier A): the ensures pin the *support* of the change —
/// every segment frame's count grows by at least one, and every *other* slot
/// is untouched. This frame condition is what lets a caller's accounting
/// telescope (it can conclude this call touched only the segment's slots).
/// Each mint targets a segment index, so a non-segment slot is simply never a
/// mint target — hence the frame condition needs no injectivity argument.
pub proof fn tracked_mint_seg_obligations(
    tracked regions: &mut MetaRegionOwners,
    range_start: usize,
    n: int,
)
    requires
        0 <= n,
        old(regions).inv(),
    ensures
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        final(regions).slot_owners == old(regions).slot_owners,
        // Counts only grow.
        forall|idx: usize|
            #![trigger final(regions).frame_obligations.count(idx)]
            final(regions).frame_obligations.count(idx) >= old(regions).frame_obligations.count(
                idx,
            ),
        // The exact per-frame mint effect (segment frames +≥1, all else fixed).
        seg_obligations_minted(*old(regions), *final(regions), range_start, n),
    decreases n,
{
    let ghost g0 = *regions;
    if n > 0 {
        tracked_mint_seg_obligations(regions, range_start, n - 1);
        let ghost gmid = *regions;
        let idx = frame_to_index((range_start + (n - 1) * PAGE_SIZE) as usize);
        let tracked _ = regions.tracked_mint_frame_obligation(idx);
        // `regions.frame_obligations == gmid.frame_obligations.insert(idx)`,
        // and the recursion already proved the strengthened ensures for the
        // first `n-1` frames against `g0`. Bridge each ensures to `n`.
        // Frame condition: a non-segment slot is untouched by the recursion
        // (it omits the slot from `[0, n-1)`) and is not the mint target.
        assert forall|jdx: usize|
            #![trigger regions.frame_obligations.count(jdx)]
            (forall|i: int|
                #![trigger frame_to_index((range_start + i * PAGE_SIZE) as usize)]
                0 <= i < n ==> jdx != frame_to_index(
                    (range_start + i * PAGE_SIZE) as usize,
                )) implies regions.frame_obligations.count(jdx) == g0.frame_obligations.count(
            jdx,
        ) by {};
        // Each segment frame gained at least one entry.
        assert forall|i: int|
            #![trigger frame_to_index((range_start + i * PAGE_SIZE) as usize)]
            0 <= i < n implies regions.frame_obligations.count(
            frame_to_index((range_start + i * PAGE_SIZE) as usize),
        ) >= g0.frame_obligations.count(frame_to_index((range_start + i * PAGE_SIZE) as usize))
            + 1 by {
            // i < n-1: recursion gives `gmid.count(idx_i) >= g0.count(idx_i)+1`;
            // the mint only grows counts. i == n-1: `gmid.count(idx) >= g0.count(idx)`
            // (monotone), and the mint adds exactly one at `idx`.
        };
    }
}

/// Redeems the per-frame `frame_obligations` entry for each of the first `n`
/// frames of a segment starting at `range_start` — the inverse of
/// [`tracked_mint_seg_obligations`]. Used by [`Segment::drop`] to drain the
/// segment's retained per-frame references *before* the per-frame teardown
/// loop, so that loop sees `count == 0` (as it did before the migration) and
/// its `from_raw`(+1)/`frame.drop`(-1) pair nets to zero unchanged.
///
/// Unlike minting, redeeming requires the frame indices be *distinct*
/// (redeeming one frame must not drop another's count below 1) and each count
/// be `>= 1` up front — both supplied by [`SegmentOwner::relate_regions`].
/// Leaves `slots`, `slot_owners`, and the (vestigial) range `obligations`
/// ledger untouched.
pub proof fn tracked_redeem_seg_obligations(
    tracked regions: &mut MetaRegionOwners,
    range_start: usize,
    n: int,
)
    requires
        0 <= n,
        old(regions).inv(),
        forall|i: int|
            #![trigger frame_to_index((range_start + i * PAGE_SIZE) as usize)]
            0 <= i < n ==> old(regions).frame_obligations.count(
                frame_to_index((range_start + i * PAGE_SIZE) as usize),
            ) >= 1,
        forall|i: int, j: int|
            #![trigger frame_to_index((range_start + i * PAGE_SIZE) as usize),
                frame_to_index((range_start + j * PAGE_SIZE) as usize)]
            0 <= i < j < n ==> frame_to_index((range_start + i * PAGE_SIZE) as usize)
                != frame_to_index((range_start + j * PAGE_SIZE) as usize),
    ensures
        final(regions).inv(),
        final(regions).slots == old(regions).slots,
        final(regions).slot_owners == old(regions).slot_owners,
    decreases n,
{
    if n > 0 {
        let idx = frame_to_index((range_start + (n - 1) * PAGE_SIZE) as usize);
        let tracked tok = DropObligation::tracked_mint(idx);
        regions.tracked_redeem_frame_obligation(tok);
        // Redeeming `idx` (the n-1'th frame) left every earlier frame's count
        // untouched, since the indices are distinct — so the `>= 1` hypothesis
        // still holds for `[0, n-1)` and the recursive call's precondition is met.
        assert forall|i: int|
            #![trigger frame_to_index((range_start + i * PAGE_SIZE) as usize)]
            0 <= i < n - 1 implies regions.frame_obligations.count(
            frame_to_index((range_start + i * PAGE_SIZE) as usize),
        ) >= 1 by {};
        tracked_redeem_seg_obligations(regions, range_start, n - 1);
    }
}

} // verus!
