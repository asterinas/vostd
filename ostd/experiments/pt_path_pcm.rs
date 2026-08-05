//! **The same composition, in raw resource logic.**
//!
//! [`super::pt_path_tsm`] builds a page-table entry that holds a PtPath
//! reference to a frame, as a second `tokenized_state_machine!`, and proves
//!
//! > *this entry's presence implies the frame's count includes it*
//!
//! This file does the same thing on the PCM of [`super::rc_pcm`], so the two can
//! be compared line for line. See [`super`] for the comparison.
use vstd::prelude::*;
use vstd::resource::pcm::Resource;
use vstd::resource::Loc;

use super::rc_pcm::{auth, readers, RcCarrier};
use super::rc_tsm::RcState;

verus! {

/// A page-table entry holding a PtPath reference.
///
/// Note what is *absent*: no state machine, no fields beyond the reference
/// itself, no transitions, no invariants, no inductive proofs. The entry simply
/// **owns a fragment** of the frame's resource. In this encoding "the entry is
/// installed" is not a modelled state — it is the fact that this struct exists.
pub tracked struct PtEntryPcm {
    pub tracked ref_held: Resource<RcCarrier>,
}

impl PtEntryPcm {
    /// The entry holds one reader-unit at the frame's location.
    pub open spec fn wf(self, loc: Loc) -> bool {
        &&& self.ref_held.loc() == loc
        &&& self.ref_held.value() == readers(1)
    }
}

/// **The composition property.** From "this entry holds a PtPath reference" and
/// the authority's band, conclude the count includes it (`n >= 1`).
///
/// The entire proof is one `validate_2`: composing what I hold with what the
/// invariant holds must be *valid*, and validity of that composition says
/// `readers <= n`, i.e. `1 <= n`.
///
/// There is no cross-machine plumbing because there are no machines — both
/// parties hold pieces of the same resource, so the relation is just validity of
/// their composition.
pub proof fn pcm_entry_implies_shared(
    tracked entry: &mut PtEntryPcm,
    tracked auth_res: &Resource<RcCarrier>,
    loc: Loc,
    n: nat,
)
    requires
        old(entry).wf(loc),
        auth_res.loc() == loc,
        auth_res.value() == auth(RcState::Shared(n)),
    ensures
        *final(entry) == *old(entry),
        1 <= n,
{
    entry.ref_held.validate_2(auth_res);
}

/// **Install**, for comparison with `PtNode::install`.
///
/// Taking ownership of the fragment *is* the installation — there is no
/// transition to fire and nothing to prove, because the resource does not
/// change. It only changes hands.
pub proof fn pcm_install(tracked frag: Resource<RcCarrier>, loc: Loc) -> (tracked res: PtEntryPcm)
    requires
        frag.loc() == loc,
        frag.value() == readers(1),
    ensures
        res.wf(loc),
{
    PtEntryPcm { ref_held: frag }
}

/// **Uninstall**, for comparison with `PtNode::uninstall`. Likewise nothing to
/// prove: the fragment comes back out exactly as it went in, and — unlike the
/// TSM's `withdraw` — it arrives already carrying its own identity, so there is
/// no re-export `assert` to remember.
pub proof fn pcm_uninstall(tracked entry: PtEntryPcm, loc: Loc) -> (tracked res: Resource<
    RcCarrier,
>)
    requires
        entry.wf(loc),
    ensures
        res.loc() == loc,
        res.value() == readers(1),
{
    let tracked PtEntryPcm { ref_held } = entry;
    ref_held
}

} // verus!
