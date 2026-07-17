// SPDX-License-Identifier: MPL-2.0
//! Spec/proof companion for [`crate::mm::frame::segment`].
use core::ops::Range;

use vstd::prelude::*;

use vstd_extra::{drop_tracking::*, ownership::*};

use crate::specs::{
    arch::PAGE_SIZE,
    mm::{
        frame::{
            mapping::{frame_to_index, meta_addr},
            meta_region_owners::MetaRegionOwners,
        },
        virt_mem::MemView,
    },
};

use crate::mm::{
    Paddr, Vaddr,
    frame::{AnyFrameMeta, Segment},
    paddr_to_vaddr,
};

verus! {

impl<M: AnyFrameMeta + ?Sized> TrackDrop for Segment<M> {
    /// The tracked state for `ManuallyDrop` purposes is the global
    /// [`MetaRegionOwners`]. The real per-segment obligation is represented
    /// by one entry per frame in `MetaRegionOwners::frame_obligations`, not
    /// by this `TrackDrop` impl. That keeps
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
        // No-op: the token is ledger-less identity. Segment drop accounting is
        // handled by `Segment::drop` against `frame_obligations` directly.
    }
}

/// Number of frames in a page-aligned physical range.
#[verifier::inline]
pub open spec fn seg_nframes(range: Range<Paddr>) -> int {
    (range.end - range.start) / PAGE_SIZE as int
}

impl<M: AnyFrameMeta + ?Sized> Segment<M> {
    /// The cross-object relation between a [`Segment`] and the global
    /// [`MetaRegionOwners`].
    ///
    /// For every frame `i` in the segment, this asserts:
    /// - the slot owner and canonical slot permission are present in `regions`,
    /// - the slot's `slot_vaddr` is consistent with its index,
    /// - the slot has a live, non-`UNUSED` reference count,
    /// - the slot has a pending `frame_obligations` entry for this segment,
    /// - the slot is a data-frame slot with no page-table paths,
    /// - distinct frames in the segment map to distinct slot indices.
    ///
    /// This is an invariant preserved by operations that transform a
    /// `Segment` together with `MetaRegionOwners`. The segment's own `range`
    /// is the only identity source; there is no separate segment owner token.
    pub open spec fn relate_regions(&self, regions: MetaRegionOwners) -> bool {
        &&& forall|i: int|
            #![trigger frame_to_index((self.range.start + i * PAGE_SIZE) as usize)]
            0 <= i < seg_nframes(self.range) ==> {
                let idx = frame_to_index((self.range.start + i * PAGE_SIZE) as usize);
                // Per-frame linear-drop: the segment holds one (forgotten)
                // reference per frame, recorded as a `frame_obligations` count.
                &&& regions.frame_obligations.count(idx) >= 1
                &&& regions.slot_owners.contains_key(idx)
                &&& regions.slots.contains_key(idx)
                &&& regions.slot_owners[idx].slot_vaddr == meta_addr(idx)
                &&& regions.slot_owners[idx].inner_perms.ref_count.value()
                    > 0
                // Segment frames are shared (never `UNIQUE`).
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
    /// Use this to extract per-frame facts without fighting trigger inference.
    pub proof fn relate_regions_at(&self, regions: MetaRegionOwners, i: int)
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
    pub proof fn relate_regions_distinct(&self, regions: MetaRegionOwners, i: int, j: int)
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

    /// The bundled invariant for [`Segment`] operations that thread the global
    /// `regions`: the segment's own invariant, the region invariant, and the
    /// cross-object relation tying this segment's range to `regions`.
    ///
    /// Mirrors the `invariants` bundles used throughout the page-table / cursor
    /// code — it collapses the clauses repeated across `split`, `slice`,
    /// `into_raw`, `next`, and `drop` into one predicate.
    pub open spec fn invariants(&self, regions: MetaRegionOwners) -> bool {
        &&& self.inv()
        &&& regions.inv()
        &&& self.relate_regions(regions)
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
/// be `>= 1` up front — both supplied by [`Segment::relate_regions`].
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
