//! **Probe: can a second machine consume the refcount machine?**
//!
//! The refcount TSM works beautifully *as a closed protocol over one cell*. The
//! open question for the whole-`mm` goal is whether it survives being **consumed
//! by a higher-level machine** — because the plan's endgame (Phases 5–8) has the
//! page-table layer, `Segment`, and `Frame` handles all holding kind-tagged
//! references into the same per-slot count.
//!
//! This encodes the smallest real instance of that: a page-table entry that,
//! while installed, holds a **PtPath reference** to a frame. The property under
//! test is the one Phase 6 needs —
//!
//! > *this entry's presence implies the frame's count includes it*
//!
//! — stated across two independent machines ([`PtNode`] here, `FrameRc` there).
//!
//! # What this is really testing
//!
//! Not whether a bigger machine can *store* another machine's tokens — that much
//! is obviously allowed. The question is whether a fact **relating the two
//! machines' states** is reachable at all, given that:
//!
//! - a `transition!` body is a closed DSL with no way to call another machine's
//!   transition, and
//! - a machine's `#[invariant]` ranges only over its own fields, so `PtNode`
//!   cannot mention `FrameRc`'s band directly.
//!
//! If the answer is yes, TSMs compose well enough for the whole-`mm` program and
//! the ~4× cost of hand-written PCM (see [`super::rc_pcm`]) buys only
//! ergonomics. If the answer is no, that cost buys the architecture.
//!
//! Delete once the question is settled.
use verus_state_machines_macros::tokenized_state_machine;
use vstd::invariant::*;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

use super::rc_tsm::*;
use vstd_extra::panic::may_panic;

verus! {

/// A single page-table entry, as its own tokenized state machine.
///
/// The entry is either absent, or installed and holding one **PtPath reference**
/// to the frame it points at. That reference is a `FrameRc::reader` token —
/// literally the same linear token a `Frame` handle holds, which is what makes
/// the count include it.
tokenized_state_machine!(PtNode {
    fields {
        /// Which frame machine this entry's reference belongs to. Constant, so
        /// every token of this instance agrees on it without further plumbing.
        #[sharding(constant)]
        pub rc_instance: InstanceId,

        /// Ghost view of the reference held below — the token's spec value, not
        /// the token. This copy is what makes [`guard_ref`] legal: a `guard`
        /// value must be a deterministic function of the caller's inputs, so the
        /// caller has to be able to *name* the reference it is borrowing. A bare
        /// `present: bool` cannot name it.
        #[sharding(variable)]
        pub ref_view: Option<FrameRc::reader<()>>,

        /// The reference itself, parked here for exactly as long as the entry is
        /// installed. Storage-sharded because it is a *tracked* token being held,
        /// not ghost data being described.
        ///
        /// **It is not a path.** It carries no location: it says only "a
        /// reference to that frame is held *here*". *Where* here is — the
        /// `TreePath` that `paths_in_pt` would record — is implicit in which
        /// `PtNode` instance you are looking at, and is deliberately unmodelled.
        /// "PtPath" in `TOKENIZATION_PLAN.md` names the *kind* of reference (one
        /// held by a page table, as against a `Frame` handle or a `Segment`
        /// cover), not a path value.
        #[sharding(storage_option)]
        pub ref_held: Option<FrameRc::reader<()>>,
    }

    /// The ghost view and the parked token are the same reference. This is what
    /// makes "the entry is installed" mean something to the frame layer.
    #[invariant]
    pub fn view_matches_held(&self) -> bool {
        self.ref_view == self.ref_held
    }

    /// The held reference belongs to *this* entry's frame machine.
    #[invariant]
    pub fn ref_belongs(&self) -> bool {
        self.ref_held is Some ==> self.ref_held->0.instance_id() == self.rc_instance
    }

    init!{
        empty(rc_inst: InstanceId) {
            init rc_instance = rc_inst;
            init ref_view = Option::None;
            init ref_held = Option::None;
        }
    }

    #[inductive(empty)]
    fn empty_inductive(post: Self, rc_inst: InstanceId) { }

    transition!{
        // Cursor `map`: install the entry, consuming a PtPath reference minted
        // from the frame machine's `do_clone`.
        install(tok: FrameRc::reader<()>) {
            require(pre.ref_view is None);
            require(tok.instance_id() == pre.rc_instance);
            update ref_view = Option::Some(tok);
            deposit ref_held += Some(tok);
        }
    }

    #[inductive(install)]
    fn install_inductive(pre: Self, post: Self, tok: FrameRc::reader<()>) { }

    transition!{
        // Cursor `unmap`: take the entry down and hand the reference back, to be
        // released by the frame machine's `dec_*`.
        uninstall(tok: FrameRc::reader<()>) {
            require(pre.ref_view == Option::Some(tok));
            // Same re-export as in `guard_ref`, and for the same reason: without
            // it the *withdrawn* token is anonymous, and the frame machine will
            // not accept it for `dec_*`. Every crossing needs its own `assert`.
            assert(tok.instance_id() == pre.rc_instance);
            withdraw ref_held -= Some(tok);
            update ref_view = Option::None;
        }
    }

    #[inductive(uninstall)]
    fn uninstall_inductive(pre: Self, post: Self, tok: FrameRc::reader<()>) { }

    property!{
        // **The cross-machine hinge.** While the entry is installed, borrow the
        // reference it holds. This is what lets a caller reach a `FrameRc` fact
        // starting from a `PtNode` fact.
        guard_ref(tok: FrameRc::reader<()>) {
            require(pre.ref_view == Option::Some(tok));
            // Re-export `ref_belongs`. A machine's `#[invariant]`s are *not*
            // visible to callers — only what a transition/property `assert`s
            // becomes an `ensures`. Without this line the borrowed reference is
            // an anonymous `FrameRc::reader` that the frame machine will refuse,
            // because nothing ties it to the right instance.
            assert(tok.instance_id() == pre.rc_instance);
            guard ref_held >= Some(tok);
        }
    }
});

/// **The composed step: cursor `map`.** Mint a PtPath reference off an existing
/// handle and install it into the entry — the two machines moving together.
///
/// # On atomicity
///
/// These two moves cannot be one hardware atomic, and should not be: the
/// refcount lives in a shared cell (so its bump is a CAS under
/// `open_atomic_invariant!`), while the entry is protected by the node lock (so
/// the caller holds its `entry` token exclusively, modelled here as `&mut`).
/// Only the first needs to be atomic with respect to other threads.
///
/// # The in-flight window, and why it is sound
///
/// Between the CAS and the install, the caller holds a reference that no
/// registry owns. Another thread reading `ref_count` sees the bump before any
/// entry exists to justify it. That is fine, and worth being precise about:
///
/// - `FrameRc`'s own invariant `counter == |reader|` is **never** violated — the
///   in-flight token is still a token, held by this thread;
/// - `PtNode`'s invariant `entry == path` is **never** violated — both are still
///   `None`;
/// - what *is* transiently untrue is the **decomposition by registry**
///   (`rc == H + P + cover`), because this reference is in a hand rather than in
///   a registry.
///
/// So the plan's accounting equation is a **quiescent-boundary** property, not a
/// running invariant — and token linearity is what makes the transient benign,
/// since a reference in flight is conserved rather than lost.
pub fn probe_map_step(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<()>>,
    Tracked(handle): Tracked<&FrameRc::reader<()>>,
    Tracked(pt_inst): Tracked<&PtNode::Instance>,
    Tracked(ref_view): Tracked<&mut PtNode::ref_view>,
) -> (res: bool)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        handle.instance_id() == rc.inst.id(),
        pt_inst.rc_instance() == rc.inst.id(),
        old(ref_view).instance_id() == pt_inst.id(),
        old(ref_view).value() is None,
        may_panic(),
    ensures
        final(ref_view).instance_id() == pt_inst.id(),
        res == (final(ref_view).value() is Some),
{
    if let Some(tok) = tsm_try_inc_ref_count::<()>(slot, idx, Tracked(rc), Tracked(handle)) {
        let tracked t = tok.get();
        // ---- in-flight: the count includes this reference; no entry holds it ----
        proof {
            pt_inst.install(t, ref_view, t);
        }
        true
    } else {
        false
    }
}

/// **The composed step: cursor `unmap`.** Take the entry down and release its
/// reference — the same two machines, in the opposite order.
///
/// The in-flight window is mirrored: the entry is already gone while the count
/// still includes the reference this thread is carrying to the decrement. If it
/// turns out to be the last reference, the teardown window opens and the slot
/// goes back to the free pool — the `Some` branch below.
pub fn probe_unmap_step(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<()>>,
    Tracked(pt_inst): Tracked<&PtNode::Instance>,
    Tracked(ref_view): Tracked<&mut PtNode::ref_view>,
)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        pt_inst.rc_instance() == rc.inst.id(),
        old(ref_view).instance_id() == pt_inst.id(),
        old(ref_view).value() is Some,
    ensures
        final(ref_view).instance_id() == pt_inst.id(),
        final(ref_view).value() is None,
{
    let tracked tok = pt_inst.uninstall(old(ref_view).value()->0, ref_view);
    // ---- in-flight: the entry is gone; the count still includes this reference ----
    if let Some(pair) = tsm_dec_ref_count::<()>(slot, idx, Tracked(rc), Tracked(tok)) {
        // That was the last reference: we now own the teardown window.
        let tracked perm = pair.0.get();
        let tracked permit = pair.1.get();
        tsm_recycle::<()>(slot, idx, Tracked(rc), Tracked(permit), Tracked(perm));
    }
}

/// **The experiment.** From "this page-table entry is installed", conclude that
/// the frame's physical `ref_count` is in the shared band — i.e. the count
/// includes this entry's reference.
///
/// The two machines never mention each other. The chain is:
///
/// 1. `PtNode::guard_ref` turns the entry's `present` token into a borrow of the
///    `FrameRc::reader` token it is holding;
/// 2. that reader token, inside the frame's atomic invariant, fires
///    `FrameRc::reader_implies_shared`, pinning the band to `Shared(n)`;
/// 3. `lemma_state_from_value` converts the band to the physical encoding.
///
/// Step 2 is only available *inside* `open_atomic_invariant!`, because it needs
/// the frame's `state` token — which is exactly where a real op would be anyway.
pub fn probe_entry_implies_shared(
    slot: &MetaSlot,
    idx: usize,
    Tracked(rc): Tracked<&FrameRcSlot<()>>,
    Tracked(pt_inst): Tracked<&PtNode::Instance>,
    Tracked(ref_view): Tracked<&PtNode::ref_view>,
) -> (res: u64)
    requires
        rc.wf(slot.ref_count.id(), idx as int),
        pt_inst.rc_instance() == rc.inst.id(),
        ref_view.instance_id() == pt_inst.id(),
        ref_view.value() is Some,
    ensures
        1 <= res < REF_COUNT_MAX,
{
    let res;
    open_atomic_invariant!(rc.inv.borrow() => g => {
        let tracked FrameRcGhost { rc_perm, rc_token } = g;

        proof {
            // (1) entry is installed  ⟹  we may borrow its PtPath reference
            let tracked reader = pt_inst.guard_ref(ref_view.value()->0, ref_view);
            // (2) that reference pins the frame's band to `Shared(n)`
            rc.inst.reader_implies_shared(reader.element(), &rc_token, reader);
            // (3) `Shared(n)` decodes to a physical value in `1..MAX`
            lemma_state_from_value(rc_token.value());
        }

        res = slot.ref_count.load(Tracked(&rc_perm));

        proof { g = FrameRcGhost { rc_perm, rc_token }; }
    });
    res
}

} // verus!
