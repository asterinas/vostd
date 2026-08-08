//! A **tokenized state machine (TSM)** for the per-slot frame reference count.
//!
//! The physical atomic is bound to the TSM through an
//! [`vstd::invariant::AtomicInvariant`], so each hardware atomic op (the CAS /
//! `fetch_add` / `fetch_sub` in [`crate::mm::frame::meta`]) becomes a single-
//! instruction *transition* that moves linear **reference tokens** — the
//! interference-stable resource that callers thread instead of a `&mut`
//! permission.
//!
//! The shared-reference core is adapted from the proven `RefCounter` example
//! (`tools/verus/examples/state_machines/arc.rs`); the sentinel bands, the
//! exclusive-window permit and the UNIQUE band are this protocol's own.
//!
//! # Mapping to the real `ref_count`
//!
//! The TSM tracks a *logical* [`RcState`]. The [`FrameRcGhost`] binding maps it
//! to the physical `u64` sentinel encoding used by [`MetaSlot`] — all four
//! bands, via [`sentinel_of`]:
//!
//! | [`RcState`]  | physical `ref_count`  | meaning                                    |
//! |--------------|-----------------------|--------------------------------------------|
//! | `Unused`     | [`REF_COUNT_UNUSED`]  | slot free; storage perm parked (uninit)    |
//! | `Claimed`    | `0`                   | exclusive construction/teardown window     |
//! | `Shared(n)`  | `n` in `1..MAX`       | `n` outstanding `Frame` refs               |
//! | `Unique`     | [`REF_COUNT_UNIQUE`]  | owned by a single [`UniqueFrame`]          |
//!
//! The storage permission is **parked in the machine exactly in the `Unused` and
//! `Shared` bands** and **withdrawn in `Claimed` and `Unique`** — precisely the
//! two bands in which one thread has exclusive access to the frame's metadata
//! (`write_meta` / `drop_meta_in_place` under `Claimed`, `meta_mut` under
//! `Unique`). Token linearity is what makes that exclusivity a theorem: the
//! [`permit`](FrameRc::permit) and [`unique`](FrameRc::unique) tokens are
//! `Option`-sharded, so at most one can exist per slot.
//!
//! Transition ↔ exec-site correspondence (all in [`crate::mm::frame`]):
//!
//! | transition        | exec site                                                            |
//! |-------------------|----------------------------------------------------------------------|
//! | `claim`           | `get_from_unused`'s `compare_exchange(UNUSED, 0)`                    |
//! | `publish_shared`  | `get_from_unused`'s `store(1)` (`as_unique_ptr == false`)            |
//! | `publish_unique`  | `get_from_unused`'s `store(REF_COUNT_UNIQUE)` (`as_unique_ptr`)      |
//! | `do_clone`        | `inc_ref_count`'s `fetch_add(1)` / `get_from_in_use`'s CAS `n → n+1` |
//! | `dec_basic`       | `Frame::drop`'s `fetch_sub(1)` returning `> 1`                       |
//! | `dec_to_zero`     | `Frame::drop`'s last-ref `fetch_sub(1)` → `drop_last_in_place`       |
//! | `recycle`         | `drop_last_in_place`'s `store(REF_COUNT_UNUSED)`                     |
//! | `to_unique`       | `UniqueFrame::try_from_shared`'s CAS `1 → REF_COUNT_UNIQUE`          |
//! | `from_unique`     | `Frame::from_unique`'s `store(1)`                                    |
//! | `release_unique`  | `UniqueFrame::drop` / `reset_as_unused`'s `store(0)`                 |
//!
//! # Status — Phase 1 complete; **all ten transitions bound to real cells**
//!
//! The machine is *full-state* (all four bands, both exclusive-window tokens)
//! and verified, and every transition in the table above has a `tsm_*` binding
//! at the bottom of this file that fires it against a real `MetaSlot.ref_count`
//! — real CAS, real `fetch_sub`, real stores, each inside
//! `open_atomic_invariant!`. `tsm_try_claim` + `tsm_publish_{shared,unique}`
//! model `get_from_unused`'s two-block window *honestly*: between the calls the
//! cell physically reads `0` and the caller is provably the only party able to
//! touch the metadata, because it holds the only permit.
//!
//! It is still not *load-bearing*: production `mm` code holds none of these
//! tokens, because the spikes take their token bundle as parameters rather than
//! out of [`MetaRegionOwners`].
//!
//! The custody handover itself is done and needed **no axiom**: see
//! [`tracked_bind_slot`], which builds a slot's [`FrameRcSlot`] bundle from its
//! two permissions, soundly, by binding at boot while the cell still reads
//! [`REF_COUNT_UNUSED`].
//!
//! What remains (see `TOKENIZATION_PLAN.md`):
//!  - **Phase 2.** Give up the permissions. `MetaSlotOwner.inner_perms` holds
//!    `ref_count`/`storage` as plain fields threaded by `&mut`; the region must
//!    hand them to [`tracked_bind_slot`] and keep no copy. This is a structural
//!    change to `MetaSlotOwner`, and it is where the
//!    599-direct-reads-vs-4-through-the-bridge problem bites.
//!  - **Phase 3.** Rewrite the remaining `meta.rs` / `unique.rs` atomic ops.
//!    **Not** by deriving today's value-level `ensures` from the tokens as the
//!    plan originally assumed: `final(rc).value() == old(rc).value() + 1` is not
//!    expressible once the cell is shared, since no pre- or post-value of it is
//!    stable under interference. Consumers of such postconditions move to
//!    tokens. [`lemma_state_from_value`] bridges the *band*, not the value.
use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::shared::Shared;

// The real sentinel constants this TSM is designed to be bound against.
pub use crate::mm::frame::meta::{MetaSlot, REF_COUNT_MAX, REF_COUNT_UNIQUE, REF_COUNT_UNUSED};
use vstd_extra::panic::may_panic;

verus! {

/// The logical state of one slot's reference count: the four physical bands of
/// [`MetaSlot::ref_count`](crate::mm::frame::meta::MetaSlot::ref_count) as a
/// ghost enum. See [`sentinel_of`] for the physical encoding.
pub ghost enum RcState {
    /// Physically [`REF_COUNT_UNUSED`]. The slot is free; its (uninitialized)
    /// storage permission is parked in the machine.
    Unused,
    /// Physically `0`: the transient exclusive window in which one thread is
    /// constructing or tearing down the frame's metadata. The holder of the
    /// [`permit`](FrameRc::permit) token owns the withdrawn storage permission.
    Claimed,
    /// Physically `n`, with `1 <= n < REF_COUNT_MAX`: `n` outstanding shared
    /// handles, each holding one [`reader`](FrameRc::reader) token.
    Shared(nat),
    /// Physically [`REF_COUNT_UNIQUE`]: a single `UniqueFrame` owns the slot and
    /// the withdrawn storage permission, witnessed by the
    /// [`unique`](FrameRc::unique) token.
    Unique,
}

/// The physical `u64` this logical state encodes to.
pub open spec fn sentinel_of(s: RcState) -> u64 {
    match s {
        RcState::Unused => REF_COUNT_UNUSED,
        RcState::Claimed => 0,
        RcState::Shared(n) => n as u64,
        RcState::Unique => REF_COUNT_UNIQUE,
    }
}

/// The band bound that makes [`sentinel_of`] injective: a shared count is never
/// `0` (that is the `Claimed` band) and never reaches `REF_COUNT_MAX` (beyond
/// which lie the illegal overflow-guard values and the two sentinels).
pub open spec fn state_in_band(s: RcState) -> bool {
    s is Shared ==> 1 <= s->Shared_0 && s->Shared_0 < REF_COUNT_MAX as nat
}

tokenized_state_machine!(FrameRc<Perm> {
    fields {
        /// The logical band. Bound to the physical cell by [`FrameRcGhost::wf`].
        #[sharding(variable)]
        pub state: RcState,

        /// The frame's metadata storage permission. Parked in the machine in the
        /// `Unused` and `Shared` bands; withdrawn by the exec thread for the
        /// `Claimed` and `Unique` bands, where it has exclusive metadata access.
        #[sharding(storage_option)]
        pub storage: Option<Perm>,

        /// One token per outstanding shared `Frame` reference. Holding one
        /// licenses immutable access to `storage` via
        /// [`reader_guard`](Self::reader_guard).
        #[sharding(multiset)]
        pub reader: Multiset<Perm>,

        /// The in-flight permit for the transient physical-`0` window: minted by
        /// `claim` / `dec_to_zero` / `release_unique`, consumed by
        /// `publish_shared` / `publish_unique` / `recycle`. Being `Option`-
        /// sharded, it is the linear proof that the window has one owner.
        #[sharding(option)]
        pub permit: Option<()>,

        /// The witness of the `Unique` band, held by the `UniqueFrame`.
        #[sharding(option)]
        pub unique: Option<()>,
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: Perm| self.reader.count(t) > 0 ==> self.storage == Option::Some(t)
    }

    /// The storage permission is in the machine exactly in the two
    /// non-exclusive bands.
    #[invariant]
    pub fn storage_parked_iff_not_exclusive(&self) -> bool {
        self.storage is Some <==> (self.state is Unused || self.state is Shared)
    }

    /// In the `Shared` band the count is in range and is *exactly* the number of
    /// outstanding reader tokens — the equation the whole protocol exists for.
    #[invariant]
    pub fn shared_band_wf(&self) -> bool {
        self.state is Shared ==> {
            &&& 1 <= self.state->Shared_0
            &&& self.state->Shared_0 < REF_COUNT_MAX as nat
            &&& self.storage is Some
            &&& self.reader.count(self.storage->0) == self.state->Shared_0
        }
    }

    /// Outside the `Shared` band there are no shared handles at all.
    #[invariant]
    pub fn no_readers_outside_shared(&self) -> bool {
        !(self.state is Shared) ==> forall |t: Perm| self.reader.count(t) == 0
    }

    #[invariant]
    pub fn permit_iff_claimed(&self) -> bool {
        self.permit is Some <==> self.state is Claimed
    }

    #[invariant]
    pub fn unique_iff_unique_band(&self) -> bool {
        self.unique is Some <==> self.state is Unique
    }

    init!{
        // The slot is born free (physical `REF_COUNT_UNUSED`), with its
        // uninitialized storage permission parked in the machine.
        initialize_unused(x: Perm) {
            init state = RcState::Unused;
            init storage = Option::Some(x);
            init reader = Multiset::empty();
            init permit = Option::None;
            init unique = Option::None;
        }
    }

    #[inductive(initialize_unused)]
    fn initialize_unused_inductive(post: Self, x: Perm) {
        broadcast use group_multiset_axioms;
    }

    transition!{
        // `compare_exchange(REF_COUNT_UNUSED, 0)`: take the exclusive window and
        // withdraw the (uninitialized) storage permission to write metadata into.
        claim() {
            require(pre.state is Unused);
            birds_eye let x = pre.storage->0;
            withdraw storage -= Some(x);
            update state = RcState::Claimed;
            add permit += Some(());
        }
    }

    #[inductive(claim)]
    fn claim_inductive(pre: Self, post: Self) { }

    transition!{
        // `store(1)`: publish the constructed frame as shared, depositing the
        // now-initialized permission and taking the first reader token.
        publish_shared(x: Perm) {
            remove permit -= Some(());
            assert(pre.state is Claimed);
            update state = RcState::Shared(1);
            deposit storage += Some(x);
            add reader += {x};
        }
    }

    #[inductive(publish_shared)]
    fn publish_shared_inductive(pre: Self, post: Self, x: Perm) {
        broadcast use group_multiset_axioms;
        assert(pre.reader.count(x) == 0);
    }

    transition!{
        // `store(REF_COUNT_UNIQUE)`: publish the constructed frame as unique.
        // The permission stays with the exec thread (the `UniqueFrame`).
        publish_unique() {
            remove permit -= Some(());
            assert(pre.state is Claimed);
            update state = RcState::Unique;
            add unique += Some(());
        }
    }

    #[inductive(publish_unique)]
    fn publish_unique_inductive(pre: Self, post: Self) { }

    property!{
        // A reader token grants shared read access to the parked storage.
        reader_guard(x: Perm) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    property!{
        // All shared handles of a slot guard the same permission.
        reader_match(x: Perm, y: Perm) {
            have reader >= {x};
            have reader >= {y};
            assert(x == y);
        }
    }

    property!{
        // Holding a reader token pins the slot to the `Shared` band — hence
        // (through `FrameRcGhost::wf`) to a physical value in `1..MAX`.
        reader_implies_shared(x: Perm) {
            have reader >= {x};
            assert(pre.state is Shared);
        }
    }

    property!{
        // The permit is the exclusive right to the physical-`0` window.
        permit_implies_claimed() {
            have permit >= Some(());
            assert(pre.state is Claimed);
        }
    }

    property!{
        // The unique token pins the slot to the `Unique` band.
        unique_implies_unique_band() {
            have unique >= Some(());
            assert(pre.state is Unique);
        }
    }

    transition!{
        // `inc_ref_count` / `get_from_in_use`: `n → n+1`, mint one reader token.
        // The bound is the caller's overflow guard (the exec sites panic past it).
        do_clone(x: Perm) {
            have reader >= {x};
            require(pre.state->Shared_0 + 1 < REF_COUNT_MAX as nat);
            assert(pre.state is Shared);
            update state = RcState::Shared((pre.state->Shared_0 + 1) as nat);
            add reader += {x};
        }
    }

    #[inductive(do_clone)]
    fn do_clone_inductive(pre: Self, post: Self, x: Perm) {
        broadcast use group_multiset_axioms;
        assert(pre.reader.count(x) > 0);
        assert(pre.storage == Option::Some(x));
    }

    transition!{
        // `Frame::drop`, not the last ref: `n → n-1` with `n ≥ 2`.
        dec_basic(x: Perm) {
            remove reader -= {x};
            assert(pre.state is Shared);
            require(pre.state->Shared_0 >= 2);
            update state = RcState::Shared((pre.state->Shared_0 - 1) as nat);
        }
    }

    #[inductive(dec_basic)]
    fn dec_basic_inductive(pre: Self, post: Self, x: Perm) {
        broadcast use group_multiset_axioms;
        assert(pre.storage == Option::Some(x));
    }

    transition!{
        // `Frame::drop`, the last ref: `1 → 0`. Withdraw the storage permission
        // and hand it, with the window permit, to `drop_last_in_place`.
        dec_to_zero(x: Perm) {
            remove reader -= {x};
            assert(pre.state is Shared);
            require(pre.state->Shared_0 < 2);
            assert(pre.state->Shared_0 == 1);
            update state = RcState::Claimed;
            withdraw storage -= Some(x);
            add permit += Some(());
        }
    }

    #[inductive(dec_to_zero)]
    fn dec_to_zero_inductive(pre: Self, post: Self, x: Perm) {
        broadcast use group_multiset_axioms;
        assert(pre.storage == Option::Some(x));
        assert forall |t: Perm| post.reader.count(t) == 0 by {
            if t != x {
                assert(pre.reader.count(t) == 0);
            }
        }
    }

    transition!{
        // `drop_last_in_place`'s `store(REF_COUNT_UNUSED)`: close the exclusive
        // window by returning the (again uninitialized) permission to the machine.
        recycle(x: Perm) {
            remove permit -= Some(());
            assert(pre.state is Claimed);
            update state = RcState::Unused;
            deposit storage += Some(x);
        }
    }

    #[inductive(recycle)]
    fn recycle_inductive(pre: Self, post: Self, x: Perm) { }

    transition!{
        // `UniqueFrame::try_from_shared`: CAS `1 → REF_COUNT_UNIQUE`. The sole
        // reader is exchanged for the unique token plus the storage permission.
        to_unique(x: Perm) {
            remove reader -= {x};
            assert(pre.state is Shared);
            require(pre.state->Shared_0 == 1);
            update state = RcState::Unique;
            withdraw storage -= Some(x);
            add unique += Some(());
        }
    }

    #[inductive(to_unique)]
    fn to_unique_inductive(pre: Self, post: Self, x: Perm) {
        broadcast use group_multiset_axioms;
        assert(pre.storage == Option::Some(x));
        assert forall |t: Perm| post.reader.count(t) == 0 by {
            if t != x {
                assert(pre.reader.count(t) == 0);
            }
        }
    }

    transition!{
        // `Frame::from_unique`: `store(1)`. The unique token is exchanged for the
        // first reader token, and the permission goes back into the machine.
        from_unique(x: Perm) {
            remove unique -= Some(());
            assert(pre.state is Unique);
            update state = RcState::Shared(1);
            deposit storage += Some(x);
            add reader += {x};
        }
    }

    #[inductive(from_unique)]
    fn from_unique_inductive(pre: Self, post: Self, x: Perm) {
        broadcast use group_multiset_axioms;
        assert(pre.reader.count(x) == 0);
    }

    transition!{
        // `UniqueFrame::drop` / `reset_as_unused`: `store(0)`. The unique owner
        // steps down into the exclusive teardown window, keeping the permission.
        release_unique() {
            remove unique -= Some(());
            assert(pre.state is Unique);
            update state = RcState::Claimed;
            add permit += Some(());
        }
    }

    #[inductive(release_unique)]
    fn release_unique_inductive(pre: Self, post: Self) { }
});

/// Distinct in-band logical states have distinct physical encodings — so a
/// single atomic read of `ref_count` determines the band unambiguously.
pub proof fn lemma_sentinel_injective(s1: RcState, s2: RcState)
    requires
        state_in_band(s1),
        state_in_band(s2),
        sentinel_of(s1) == sentinel_of(s2),
    ensures
        s1 == s2,
{
    assert(REF_COUNT_MAX < REF_COUNT_UNIQUE) by (compute);
}

/// The band decoder used by the exec ops: from the physical value read out of
/// the cell, conclude which logical band the (in-band) state is in.
pub proof fn lemma_state_from_value(s: RcState)
    requires
        state_in_band(s),
    ensures
        sentinel_of(s) == REF_COUNT_UNUSED <==> s is Unused,
        sentinel_of(s) == REF_COUNT_UNIQUE <==> s is Unique,
        sentinel_of(s) == 0 <==> s is Claimed,
        (1 <= sentinel_of(s) && sentinel_of(s) < REF_COUNT_MAX) <==> s is Shared,
        s is Shared ==> sentinel_of(s) == s->Shared_0,
{
    assert(REF_COUNT_MAX < REF_COUNT_UNIQUE) by (compute);
}

/// A standalone exercise of the **generated token API**: one slot driven around
/// its whole lifecycle, firing every transition at least once and checking the
/// band the `state` token lands in.
///
/// The physical cell is absent here — this is purely the token algebra that
/// Phase 3 will run *inside* `open_atomic_invariant!` against the real
/// `ref_count`. Its job is to pin down the call shapes (what each transition
/// consumes and returns) before exec code depends on them, and to demonstrate
/// that the two lifecycles compose: shared ⇄ unique, and both back to free.
pub proof fn lifecycle_smoke_test<Perm>(tracked p_uninit: Perm, tracked p_meta: Perm) {
    // Boot: the slot is born free, its uninitialized permission parked inside.
    let tracked (Tracked(inst), Tracked(mut st), Tracked(_readers), Tracked(_pm), Tracked(_un)) =
        FrameRc::Instance::initialize_unused(p_uninit, Option::Some(p_uninit));
    assert(st.value() is Unused);

    // `get_from_unused`: CAS UNUSED → 0. The permission comes out with the permit.
    let tracked (_, Tracked(perm), Tracked(permit)) = inst.claim(&mut st);
    assert(st.value() is Claimed);
    inst.permit_implies_claimed(&st, &permit);

    // `write_meta` happens here (`perm` → `p_meta`), then `store(1)`.
    let tracked r0 = inst.publish_shared(p_meta, &mut st, p_meta, permit);
    assert(st.value() == RcState::Shared(1));

    // `inc_ref_count`: 1 → 2, then `Frame::drop` of the clone: 2 → 1.
    let tracked r1 = inst.do_clone(p_meta, &mut st, &r0);
    assert(st.value() == RcState::Shared(2));
    inst.reader_match(p_meta, p_meta, &r0, &r1);
    let _ = inst.reader_guard(p_meta, &r0);
    inst.dec_basic(p_meta, &mut st, r1);
    assert(st.value() == RcState::Shared(1));
    inst.reader_implies_shared(p_meta, &st, &r0);

    // `UniqueFrame::try_from_shared`: CAS 1 → REF_COUNT_UNIQUE, and back again.
    let tracked (Tracked(perm), Tracked(uniq)) = inst.to_unique(p_meta, &mut st, r0);
    assert(st.value() is Unique);
    inst.unique_implies_unique_band(&st, &uniq);
    let tracked r2 = inst.from_unique(p_meta, &mut st, perm, uniq);
    assert(st.value() == RcState::Shared(1));

    // `Frame::drop` of the last handle: 1 → 0, then `drop_last_in_place`.
    let tracked (Tracked(perm), Tracked(permit)) = inst.dec_to_zero(p_meta, &mut st, r2);
    assert(st.value() is Claimed);
    inst.recycle(perm, &mut st, perm, permit);
    assert(st.value() is Unused);

    // The unique branch of construction: CAS UNUSED → 0, `store(REF_COUNT_UNIQUE)`,
    // then `UniqueFrame::drop`'s `store(0)` and back to free.
    let tracked (_, Tracked(perm), Tracked(permit)) = inst.claim(&mut st);
    let tracked uniq = inst.publish_unique(&mut st, permit);
    assert(st.value() is Unique);
    let tracked permit = inst.release_unique(&mut st, uniq);
    assert(st.value() is Claimed);
    inst.recycle(perm, &mut st, perm, permit);
    assert(st.value() is Unused);
}

// =============================================================================
// PHASE 2/3 SPIKE — drive ONE real exec op from tokens.
//
// The scoped experiment from `TOKENIZATION_PLAN.md`: bind the machine to an
// actual `MetaSlot.ref_count` cell and run a real refcount bump as a transition,
// without restructuring `MetaRegionOwners`. The bundle (instance + invariant +
// reader token) arrives as parameters rather than out of the region, so the
// blast radius is this one function.
//
// What it establishes, beyond the Phase 0 de-risk (which used a synthetic cell):
//  - the per-slot `AtomicInvariant` opens around a *real* `MetaSlot` field;
//  - `do_clone` discharges against the CAS postcondition via the sentinel
//    decode, with no value-level assumption about the shared cell;
//  - the overflow guard is discharged from the *checked load*, so no out-of-band
//    value is ever written.
//
// FINDING — WHY THIS IS THE CAS FORM, NOT `inc_ref_count`'s `fetch_add`.
// The plan orders Phase 3 "easiest→hardest: inc_ref_count → get_from_in_use
// (CAS-retry) → ...". That ordering is backwards. `inc_ref_count` increments
// *first* and checks after, so inside the invariant the cell is already bumped
// and the token must move somewhere before the invariant can be re-established.
// That forces an out-of-band state — and a single saturation state does not
// close: entering it again bumps the cell past `REF_COUNT_MAX`, with no
// transition to absorb the result. Modelling it properly means reproducing the
// whole `REF_COUNT_MAX..REF_COUNT_UNIQUE` guard band from `MetaSlot`'s docs as
// live machine states. `get_from_in_use`'s load-check-CAS pattern has none of
// this: the CAS only succeeds if the value is still the checked one, so the cell
// never leaves the legal band and the machine needs no saturation state at all.
//
// Consequence for Phase 3: do the CAS ops first, and treat `inc_ref_count` as a
// separate decision — either model the guard band, or re-implement it as a CAS
// loop (it is already the only op that bumps blind).
// =============================================================================
/// Token-driven refcount bump on a real `MetaSlot.ref_count`, in the load-check-CAS
/// shape of `MetaSlot::get_from_in_use`. One CAS attempt; on failure the caller
/// retries (the real op wraps this in a spin loop).
///
/// The caller passes a **reader token** instead of `&mut PermissionU64` and gets a
/// second reader token back for the new handle.
///
/// # What the contract can and cannot say
///
/// Today's op ensures `final(rc_perm).value() == old(rc_perm).value() + 1`. That
/// claim is **not expressible here, and that is the point**: the cell is shared,
/// so no pre- or post-value of it is stable under interference. What survives is
/// the linear statement — *the caller now holds one more reader token* — with
/// `counter == |reader|` carrying the accounting.
///
/// The saturation guard degrades the same way: `inc_ref_count` can say
/// `old(rc_perm).value() >= REF_COUNT_MAX ==> may_panic()`, but a precondition
/// naming the current value of a shared cell is meaningless, so this takes the
/// unconditional `may_panic()` (the Arc-style saturation convention).
pub fn tsm_try_inc_ref_count<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
    Tracked(reader): Tracked<&FrameRc::reader<Perm>>,
) -> (res: Option<Tracked<FrameRc::reader<Perm>>>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        reader.instance_id() == rc.inst.id(),
        may_panic(),
    ensures
        res matches Some(r) ==> r@.instance_id() == rc.inst.id() && r@.element()
            == reader.element(),
{
    // Read the current count. Nothing about this value is stable once the
    // invariant closes — it is only a CAS candidate.
    let last;
    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm, rc_token } = g;
        last = slot.ref_count.load(Tracked(&rc_perm));
        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    if last >= REF_COUNT_MAX - 1 {
        // Same principle as `Arc::clone` / `MetaSlot::inc_ref_count`: abort rather
        // than let the count reach the guard band. Checked *before* any write, so
        // the cell never leaves `1..REF_COUNT_MAX`.
        vstd_extra::panic::panic_diverge();
    }
    let tracked mut new_reader = None;
    let res;
    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        res = slot.ref_count.compare_exchange(Tracked(&mut rc_perm), last, last + 1);

        proof {
            if res.is_ok() {
                // The CAS succeeded, so the cell held `last` at this instant and
                // `wf` decodes that to `Shared(last)` — the reader token rules out
                // every other band, and `last < REF_COUNT_MAX - 1` was checked
                // above, so `do_clone`'s overflow guard is discharged.
                rc.inst.reader_implies_shared(reader.element(), &rc_token, reader);
                lemma_state_from_value(rc_token.value());
                new_reader = Some(rc.inst.do_clone(reader.element(), &mut rc_token, reader));
            }
        }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    match res {
        Ok(_) => Some(Tracked(new_reader.tracked_unwrap())),
        Err(_) => None,
    }
}

/// Token-driven `Frame::drop`, bound to the real `MetaSlot.ref_count`: the
/// blind `fetch_sub` at [`crate::mm::frame`]'s drop path, as one transition.
///
/// # Why a blind decrement is fine where a blind increment is not
///
/// `inc_ref_count` and this share a shape — bump the cell, then look at what you
/// got — and that shape is what forced the `Overflow` dead end above. The
/// difference is not the direction of the arithmetic, it is **which bands are
/// legal at the landing site**:
///
/// - decrementing from `Shared(n)` lands on `Shared(n-1)` for `n >= 2`, and on
///   physical `0` for `n == 1` — and `0` is [`RcState::Claimed`], a *real* band
///   with a real meaning (the exclusive teardown window). Every outcome has a
///   transition, so the invariant is always re-establishable;
/// - incrementing off `Shared(REF_COUNT_MAX - 1)` lands on `REF_COUNT_MAX`,
///   which is *not* a band at all — it is the first illegal guard value.
///
/// So the machine absorbs an unchecked decrement for free, and cannot absorb an
/// unchecked increment at any price short of modelling the guard band.
///
/// Underflow needs no check either: the reader token pins the band to
/// `Shared(n)` with `n >= 1`, which discharges `fetch_sub`'s precondition
/// without assuming anything about the cell.
///
/// Returns the teardown window — the withdrawn storage permission and the
/// `permit` — exactly when this was the last reference, i.e. when the exec code
/// would go on to call `drop_last_in_place`. Consuming the reader token *is*
/// releasing the handle, so there is no way to drop twice.
pub fn tsm_dec_ref_count<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
    Tracked(reader): Tracked<FrameRc::reader<Perm>>,
) -> (res: Option<(Tracked<Perm>, Tracked<FrameRc::permit<Perm>>)>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        reader.instance_id() == rc.inst.id(),
    ensures
        res matches Some((_, permit)) ==> permit@.instance_id() == rc.inst.id(),
{
    let ghost x = reader.element();
    let tracked mut perm_opt = None;
    let tracked mut permit_opt = None;
    let last;

    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        proof {
            // Pins the band to `Shared(n)`, `n >= 1` — so the cell holds `n` and
            // the decrement cannot underflow.
            rc.inst.reader_implies_shared(x, &rc_token, &reader);
            lemma_state_from_value(rc_token.value());
        }

        last = slot.ref_count.fetch_sub(Tracked(&mut rc_perm), 1);

        proof {
            if last >= 2 {
                rc.inst.dec_basic(x, &mut rc_token, reader);
            } else {
                // `last == 1`: the cell is now `0`, i.e. `Claimed`. The machine
                // hands over the storage permission and the window permit —
                // which is precisely the right to run `drop_last_in_place`.
                let tracked (Tracked(p), Tracked(pm)) = rc.inst.dec_to_zero(x, &mut rc_token, reader);
                perm_opt = Some(p);
                permit_opt = Some(pm);
            }
        }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    if last >= 2 {
        None
    } else {
        Some((Tracked(perm_opt.tracked_unwrap()), Tracked(permit_opt.tracked_unwrap())))
    }
}

/// Token-driven `drop_last_in_place`'s closing `store(REF_COUNT_UNUSED)`, bound
/// to the real cell: the `recycle` transition.
///
/// This is the easiest binding of all, and for an instructive reason: the caller
/// holds the `permit`, so it is the sole owner of the slot for the duration.
/// There is no interference to reason about, no CAS, and no check — the store
/// simply cannot race. The permit is consumed, which is what makes the window
/// non-reenterable.
///
/// `perm` is the storage permission going back into the machine, uninitialized
/// again after the metadata teardown.
pub fn tsm_recycle<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
    Tracked(permit): Tracked<FrameRc::permit<Perm>>,
    Tracked(perm): Tracked<Perm>,
)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        permit.instance_id() == rc.inst.id(),
{
    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        slot.ref_count.store(Tracked(&mut rc_perm), REF_COUNT_UNUSED);

        proof {
            rc.inst.recycle(perm, &mut rc_token, perm, permit);
        }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });
}

/// `get_from_unused`'s opening `compare_exchange(REF_COUNT_UNUSED, 0)`: the
/// `claim` transition.
///
/// Note what this takes: **no token at all**. Acquiring a free slot is the one
/// operation that starts from nothing, and the CAS itself is what establishes
/// the precondition — success means the cell read `REF_COUNT_UNUSED`, which
/// [`lemma_state_from_value`] decodes to the `Unused` band.
///
/// On success the caller receives the withdrawn storage permission *and* the
/// window permit, i.e. exactly the right to run `write_meta`. Pairing this with
/// [`tsm_publish_shared`] / [`tsm_publish_unique`] models `get_from_unused`'s
/// two-block structure **honestly**: between the two calls the cell physically
/// reads `0` and the caller is the only party able to touch the metadata,
/// because it holds the only permit.
pub fn tsm_try_claim<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
) -> (res: Option<(Tracked<Perm>, Tracked<FrameRc::permit<Perm>>)>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
    ensures
        res matches Some((_, permit)) ==> permit@.instance_id() == rc.inst.id(),
{
    let tracked mut perm_opt = None;
    let tracked mut permit_opt = None;
    let cas;

    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        cas = slot.ref_count.compare_exchange(Tracked(&mut rc_perm), REF_COUNT_UNUSED, 0);

        proof {
            if cas.is_ok() {
                lemma_state_from_value(rc_token.value());
                let tracked (_, Tracked(p), Tracked(pm)) = rc.inst.claim(&mut rc_token);
                perm_opt = Some(p);
                permit_opt = Some(pm);
            }
        }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    match cas {
        Ok(_) => Some((Tracked(perm_opt.tracked_unwrap()), Tracked(permit_opt.tracked_unwrap()))),
        Err(_) => None,
    }
}

/// `get_from_unused`'s `store(1)` when `as_unique_ptr == false`: `publish_shared`.
/// Trades the permit for the first reader token and parks the now-initialized
/// storage permission back in the machine.
pub fn tsm_publish_shared<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
    Tracked(permit): Tracked<FrameRc::permit<Perm>>,
    Tracked(perm): Tracked<Perm>,
) -> (res: Tracked<FrameRc::reader<Perm>>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        permit.instance_id() == rc.inst.id(),
    ensures
        res@.instance_id() == rc.inst.id(),
{
    let tracked mut reader_opt = None;

    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        slot.ref_count.store(Tracked(&mut rc_perm), 1);

        proof {
            reader_opt = Some(rc.inst.publish_shared(perm, &mut rc_token, perm, permit));
        }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    Tracked(reader_opt.tracked_unwrap())
}

/// `get_from_unused`'s `store(REF_COUNT_UNIQUE)` when `as_unique_ptr`:
/// `publish_unique`. The storage permission stays with the caller — that is what
/// a `UniqueFrame` *is* — and the permit is traded for the unique witness.
pub fn tsm_publish_unique<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
    Tracked(permit): Tracked<FrameRc::permit<Perm>>,
) -> (res: Tracked<FrameRc::unique<Perm>>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        permit.instance_id() == rc.inst.id(),
    ensures
        res@.instance_id() == rc.inst.id(),
{
    let tracked mut uniq_opt = None;

    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        slot.ref_count.store(Tracked(&mut rc_perm), REF_COUNT_UNIQUE);

        proof { uniq_opt = Some(rc.inst.publish_unique(&mut rc_token, permit)); }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    Tracked(uniq_opt.tracked_unwrap())
}

/// `UniqueFrame::try_from_shared`'s `compare_exchange(1, REF_COUNT_UNIQUE)`:
/// `to_unique`. CAS success means the cell held `1`, i.e. the band was
/// `Shared(1)` and this reader was the *only* one — which is precisely the
/// condition for exclusive ownership, established by the hardware rather than
/// assumed.
///
/// On failure the reader token is handed back unchanged, so a failed upgrade
/// costs the caller nothing.
pub fn tsm_try_to_unique<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
    Tracked(reader): Tracked<FrameRc::reader<Perm>>,
) -> (res: Result<(Tracked<Perm>, Tracked<FrameRc::unique<Perm>>), Tracked<FrameRc::reader<Perm>>>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        reader.instance_id() == rc.inst.id(),
{
    let ghost x = reader.element();
    let tracked mut reader_opt = Some(reader);
    let tracked mut perm_opt = None;
    let tracked mut uniq_opt = None;
    let cas;

    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        cas = slot.ref_count.compare_exchange(Tracked(&mut rc_perm), 1, REF_COUNT_UNIQUE);

        proof {
            if cas.is_ok() {
                lemma_state_from_value(rc_token.value());
                let tracked r = reader_opt.tracked_take();
                let tracked (Tracked(p), Tracked(u)) = rc.inst.to_unique(x, &mut rc_token, r);
                perm_opt = Some(p);
                uniq_opt = Some(u);
            }
        }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    match cas {
        Ok(_) => Ok((Tracked(perm_opt.tracked_unwrap()), Tracked(uniq_opt.tracked_unwrap()))),
        Err(_) => Err(Tracked(reader_opt.tracked_unwrap())),
    }
}

/// `Frame::from_unique`'s `store(1)`: `from_unique`. The unique witness is traded
/// back for a reader token and the storage permission is re-parked. Note this
/// goes `Unique → Shared(1)` directly, with no transient `0` — matching the exec
/// code, which stores `1` rather than stepping through the teardown window.
pub fn tsm_from_unique<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
    Tracked(uniq): Tracked<FrameRc::unique<Perm>>,
    Tracked(perm): Tracked<Perm>,
) -> (res: Tracked<FrameRc::reader<Perm>>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        uniq.instance_id() == rc.inst.id(),
    ensures
        res@.instance_id() == rc.inst.id(),
{
    let tracked mut reader_opt = None;

    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        slot.ref_count.store(Tracked(&mut rc_perm), 1);

        proof { reader_opt = Some(rc.inst.from_unique(perm, &mut rc_token, perm, uniq)); }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    Tracked(reader_opt.tracked_unwrap())
}

/// `UniqueFrame::drop` / `reset_as_unused`'s `store(0)`: `release_unique`. The
/// unique owner steps down into the teardown window, keeping the storage
/// permission and taking the permit — so the follow-up is [`tsm_recycle`].
pub fn tsm_release_unique<Perm>(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<Perm>>,
    Tracked(uniq): Tracked<FrameRc::unique<Perm>>,
) -> (res: Tracked<FrameRc::permit<Perm>>)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        uniq.instance_id() == rc.inst.id(),
    ensures
        res@.instance_id() == rc.inst.id(),
{
    let tracked mut permit_opt = None;

    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm: mut rc_perm, rc_token: mut rc_token } = g;

        slot.ref_count.store(Tracked(&mut rc_perm), 0);

        proof { permit_opt = Some(rc.inst.release_unique(&mut rc_token, uniq)); }

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });

    Tracked(permit_opt.tracked_unwrap())
}

/// The ghost bundle that **wires the TSM to the real `MetaSlot.ref_count`**.
///
/// It co-locates the physical atomic's [`PermissionU64`] with the TSM's
/// `state` token so that a single [`AtomicInvariant`](vstd::invariant::AtomicInvariant)
/// (see [`FrameRcGhost::wf`]) keeps them in lock-step. This is the frame-domain
/// analogue of `GhostStuff` in `arc.rs`; there `cell` is a standalone
/// `PAtomicU64`, here `cell` is intended to be `MetaSlot.ref_count`.
pub tracked struct FrameRcGhost<Perm> {
    pub tracked rc_perm: PermissionU64,
    pub tracked rc_token: FrameRc::state<Perm>,
}

impl<Perm> FrameRcGhost<Perm> {
    /// The coherence predicate carried by the per-slot atomic invariant: the
    /// physical `u64` is the sentinel encoding of the logical band.
    ///
    /// The cell is identified by its [`AtomicCellId`] rather than by the
    /// `PAtomicU64` itself. That is what makes the invariant *constructible*:
    /// `PAtomicU64` is `external_body` and cannot be duplicated into a constant,
    /// but its id is a plain `int`. (`arc.rs` solves the same problem by storing
    /// a `Ghost<PAtomicU64>`.)
    pub open spec fn wf(self, inst_id: InstanceId, cell_id: AtomicCellId) -> bool {
        &&& self.rc_perm@.patomic == cell_id
        &&& self.rc_token.instance_id() == inst_id
        &&& state_in_band(self.rc_token.value())
        &&& self.rc_perm@.value == sentinel_of(self.rc_token.value())
    }
}

/// Invariant predicate for a single slot's ref_count cell: the [`FrameRcGhost`]
/// bundle is well-formed against the slot's `Instance` and cell id.
pub struct FrameRcPred;

impl<Perm> InvariantPredicate<(InstanceId, AtomicCellId), FrameRcGhost<Perm>> for FrameRcPred {
    open spec fn inv(k: (InstanceId, AtomicCellId), v: FrameRcGhost<Perm>) -> bool {
        v.wf(k.0, k.1)
    }
}

/// The per-slot governing bundle: the machine instance plus the atomic invariant
/// that binds it to one `MetaSlot.ref_count` cell.
///
/// This is what `MetaRegionOwners` is expected to hold one of per slot (as a
/// `Map<usize, FrameRcSlot<Perm>>`), and what every token-driven op needs in
/// order to open the cell. Holding it conveys no authority by itself — the
/// authority is in the `reader` / `permit` / `unique` tokens.
///
/// *Refinement for Phase 2:* wrap `inv` in [`vstd::shared::Shared`] so many
/// handles can hold it concurrently; kept unwrapped here to keep the groundwork
/// small.
pub tracked struct FrameRcSlot<Perm> {
    pub tracked inst: FrameRc::Instance<Perm>,
    pub tracked inv: Shared<
        AtomicInvariant<(InstanceId, AtomicCellId), FrameRcGhost<Perm>, FrameRcPred>,
    >,
}

impl<Perm> FrameRcSlot<Perm> {
    /// The bundle governs the cell `cell_id` in namespace `ns` (= the slot index).
    pub open spec fn wf(self, cell_id: AtomicCellId, ns: int) -> bool {
        &&& self.inv@.constant().0 == self.inst.id()
        &&& self.inv@.constant().1 == cell_id
        &&& self.inv@.namespace() == ns
    }

    /// Duplicate the *right to open* this slot's cell.
    ///
    /// This is what makes the bundle usable by a real handle. A `Frame<M>` is an
    /// owned value that outlives any borrow of the region, so it cannot hold
    /// `&FrameRcSlot` — it needs its own copy. [`Shared`] makes the invariant
    /// duplicable (`Shared::clone` is proof-mode), and the machine `Instance` is
    /// duplicable in the same way, so a bundle can be handed out per handle.
    ///
    /// Duplicating this conveys **no authority**: opening the invariant still
    /// requires a `reader` / `permit` / `unique` token, and those stay linear.
    /// What is shared is the *ability to look*, not the right to act.
    pub proof fn share(tracked &self) -> (tracked res: FrameRcSlot<Perm>)
        ensures
            res.inst.id() == self.inst.id(),
            res.inv@ == self.inv@,
    {
        FrameRcSlot { inst: self.inst.clone(), inv: self.inv.clone() }
    }
}

/// **The custody handover.** Take a slot's two permissions out of the sequential
/// world and put the refcount cell under the machine's governance.
///
/// This is the groundwork the spikes were missing — and, importantly, it needs
/// **no new axiom**. `FrameRc::Instance::initialize_unused` and
/// `AtomicInvariant::new` are both sound constructors; the latter's precondition
/// (`Pred::inv(k, v)`) is discharged here from `rc_perm.value() ==
/// REF_COUNT_UNUSED`, which is exactly what [`sentinel_of`] maps `Unused` to.
///
/// # Why binding happens at boot
///
/// The machine is created in the `Unused` band, so this can only adopt a slot
/// whose cell already reads [`REF_COUNT_UNUSED`] — which is precisely the state
/// `alloc_meta_frames` leaves every slot in at initialization. Binding at boot
/// therefore needs no mid-life adoption axiom: the machine is born in the same
/// state the hardware is already in. Adopting a *live* slot (say one already in
/// `Shared(n)`) would need either an extra `init!` for that band or an axiom,
/// and neither is required if the region binds all slots up front.
///
/// # What still stands between this and in-place wiring
///
/// Only one thing, and it is structural rather than axiomatic: `rc_perm` and
/// `storage` currently live inside `MetaRegionOwners.slot_owners[i].inner_perms`
/// as plain fields, threaded by `&mut`. To call this, the region must *give them
/// up* — and since there is exactly one permission per cell, it cannot keep a
/// copy. Fabricating one with `external_body` would not be a staging convenience
/// but an unsoundness (two permissions for one cell), so it is deliberately not
/// done here. The real change is to `MetaSlotOwner`'s shape, which is Phase 2.
pub proof fn tracked_bind_slot<Perm>(
    tracked rc_perm: PermissionU64,
    tracked storage: Perm,
    idx: usize,
) -> (tracked res: FrameRcSlot<Perm>)
    requires
        rc_perm.value() == REF_COUNT_UNUSED,
    ensures
        res.wf(rc_perm.id(), idx as int),
{
    let ghost cell_id = rc_perm.id();
    let tracked (Tracked(inst), Tracked(st), Tracked(_readers), Tracked(_pm), Tracked(_un)) =
        FrameRc::Instance::initialize_unused(storage, Option::Some(storage));
    let tracked g = FrameRcGhost { rc_perm, rc_token: st };
    let tracked inv = AtomicInvariant::new((inst.id(), cell_id), g, idx as int);
    FrameRcSlot { inst, inv: Shared::new(inv) }
}

// =============================================================================
// PHASE 0 SCRATCH — de-risk per-slot dynamic-namespace AtomicInvariants.
// Proves an `AtomicInvariant` keyed by a *runtime* slot index (ns = idx as int)
// can be opened around a hardware atomic. This is the foundation the per-slot
// design rests on (a `Map<usize, AtomicInvariant>` opened per-index). DELETE
// once Phase 2 exercises the real per-slot invariants.
// =============================================================================
/// Open the invariant for slot `idx` (namespace = `idx as int`, a runtime value)
/// and perform one atomic load. If this verifies, per-slot invariants keyed by
/// slot index are legal — the whole sharding approach is sound.
pub fn phase0_touch_slot<Perm>(
    idx: usize,
    cell: &PAtomicU64,
    Tracked(inv): Tracked<
        &AtomicInvariant<(InstanceId, AtomicCellId), FrameRcGhost<Perm>, FrameRcPred>,
    >,
) -> u64
    requires
        inv.constant().1 == cell.id(),
        inv.namespace() == idx as int,
{
    let res;
    open_atomic_invariant!(inv => g => {
        let tracked FrameRcGhost { rc_perm, rc_token } = g;
        // `g.wf(..)` gives `rc_perm@.patomic == inv.constant().1 == cell.id()`,
        // so the load's precondition is met.
        res = cell.load(Tracked(&rc_perm));
        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });
    res
}

/// Two distinct slots have distinct namespaces (`i != j ==> i as int != j as int`),
/// so their invariants can be opened independently — sequentially here, which is
/// the pattern every refcount op uses (each touches exactly one slot).
pub fn phase0_touch_two<Perm>(
    i: usize,
    j: usize,
    cell_i: &PAtomicU64,
    cell_j: &PAtomicU64,
    Tracked(inv_i): Tracked<
        &AtomicInvariant<(InstanceId, AtomicCellId), FrameRcGhost<Perm>, FrameRcPred>,
    >,
    Tracked(inv_j): Tracked<
        &AtomicInvariant<(InstanceId, AtomicCellId), FrameRcGhost<Perm>, FrameRcPred>,
    >,
)
    requires
        i != j,
        inv_i.constant().1 == cell_i.id(),
        inv_j.constant().1 == cell_j.id(),
        inv_i.namespace() == i as int,
        inv_j.namespace() == j as int,
{
    let _a = phase0_touch_slot::<Perm>(i, cell_i, Tracked(inv_i));
    let _b = phase0_touch_slot::<Perm>(j, cell_j, Tracked(inv_j));
}

} // verus!
