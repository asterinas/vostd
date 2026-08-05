//! Verification experiments — **not part of the proof of `ostd`**.
//!
//! Everything here is work toward giving `mm` a *concurrent* treatment, and none
//! of it is load-bearing yet: no code in `src/` or `specs/` holds any of these
//! tokens, and nothing outside this module depends on it. The dependency points
//! one way only (experiments → specs).
//!
//! # The refcount tokenization
//!
//! - [`rc_tsm`] — the per-slot `MetaSlot.ref_count` state machine (`FrameRc`):
//!   four sentinel bands, exclusive-window `permit`/`unique` tokens, ten
//!   transitions, and a `tsm_*` binding for each one that fires it against a
//!   *real* `ref_count` cell inside `open_atomic_invariant!`.
//! - [`tmp_region`] — a stand-in for the future `MetaRegionOwners`, shaped like
//!   the real one, that owns the per-slot bundles and reaches a real `MetaSlot`
//!   from a `Paddr`. **This one is destined to be ported**, not deleted: when the
//!   upstream split hands over the `ref_count` permissions, its contents move
//!   into the real region.
//!
//! # The TSM-vs-resource-logic question
//!
//! `tokenized_state_machine!` (VerusSync) is a *front end* for Verus's resource
//! logic: it generates a PCM, token types, and the frame-preserving-update
//! lemmas. Since the goal is to give the whole of `mm` a concurrent treatment —
//! with the refcount machinery *consumed by larger machines* — the question is
//! whether to stay on the TSM or drop to raw `vstd::resource::pcm::Resource`, as
//! `vstd_extra`'s `count.rs` does. These three price it:
//!
//! - [`rc_pcm`] — the refcount carrier as a hand-written PCM, with `do_clone`
//!   proved as a frame-preserving update. Prices *one transition* both ways.
//! - [`pt_path_tsm`] — a page-table entry holding a PtPath reference to a frame,
//!   as a second TSM, plus the composed `map`/`unmap` steps. Prices
//!   *composition* the TSM way.
//! - [`pt_path_pcm`] — the same composition on the PCM. Prices it the other way.
//!
//! **[`PT_PATH.md`](../experiments/PT_PATH.md) explains the `pt_path` protocol for
//! `mm` developers who have not written a state machine** — it maps the protocol
//! onto `paths_in_pt`, `accounting_inv` and the `&mut MetaRegionOwners` threading
//! you already know, and spells out the one real behavioural difference (the
//! in-flight window, and what it means for the accounting equation).
//!
//! # Side-by-side: the same composition, both ways
//!
//! The property in both columns is identical — *this entry's presence implies
//! the frame's count includes it* — and both verify.
//!
//! | | TSM ([`pt_path_tsm`]) | PCM ([`pt_path_pcm`]) |
//! |---|---|---|
//! | what the entry is | a second state machine: 3 fields, 2 invariants, 1 init, 2 transitions, 1 property, 3 inductive proofs | a struct holding one `Resource<RcCarrier>` |
//! | "entry is installed" | a modelled state (`entry: Option<..>` + `path` storage, tied by an invariant) | not modelled — it is the fact that the struct exists |
//! | install / uninstall | `deposit` / `withdraw` transitions, each with an inductive proof | move the value in / out; **nothing to prove** |
//! | reaching the cross-fact | `path_guard` property → borrow the token → `reader_implies_shared` → `lemma_state_from_value`, inside `open_atomic_invariant!` | one `validate_2` |
//! | identity plumbing | an `assert(tok.instance_id() == pre.rc_instance)` **per crossing** — invariants do not leak, so `path_guard` *and* `uninstall` each need their own | none — a fragment carries its own `loc` |
//! | naming the borrowed token | `guard` may not sit under `birds_eye`, so the entry must carry a ghost copy of *which* reference it holds | not applicable |
//! | composition proof | ~15 lines on top of the machine | 1 line |
//!
//! ## Reading of the result
//!
//! The two costs sit on **different axes**, and neither approach dominates:
//!
//! - **Per transition**, the TSM is far cheaper: `do_clone` is 13 lines against
//!   52 for the same step as a frame-preserving update (see [`rc_pcm`]), because
//!   `#[inductive]` proves `inv(pre) ∧ step ⟹ inv(post)` for a fixed pre/post
//!   while frame preservation quantifies over *arbitrary frames*.
//! - **Per composition**, the PCM is far cheaper: holding a fragment *is* the
//!   relation, so install/uninstall need no proof at all and the cross-fact is a
//!   single `validate_2`. The TSM needs a whole second machine and an explicit
//!   re-export at every boundary crossing.
//! - **On the accounting equation**, the TSM wins decisively: `counter ==
//!   |reader|` is one invariant clause. The PCM *cannot state it* — `valid_op`
//!   forces validity to be downward-closed, so every clause is an inequality
//!   (`readers <= n`), and exact counting has to be rebuilt from share
//!   conservation (`count.rs`'s `frac`). That equation is the centrepiece of
//!   `TOKENIZATION_PLAN.md` §1 and of Phases 5–7.
//!
//! So the trade is: **the TSM makes each protocol cheap and the accounting free,
//! but charges a fixed fee per protocol boundary; the PCM makes boundaries free
//! but charges per step and makes the accounting a construction.**
//!
//! For `mm` the boundary count is bounded and small — frames, page-table paths,
//! segments — while the transition count and the reliance on exact accounting
//! are large. That is why the current recommendation is to **stay on the TSM**;
//! the per-crossing fee is a real cost, but it is paid a few times, not a few
//! hundred.
#[allow(unused_parens)]
#[allow(unused_braces)]
pub mod pt_path_pcm;
#[allow(unused_parens)]
#[allow(unused_braces)]
pub mod pt_path_tsm;
#[allow(unused_parens)]
#[allow(unused_braces)]
pub mod rc_pcm;
#[allow(unused_parens)]
#[allow(unused_braces)]
pub mod rc_tsm;
#[allow(unused_parens)]
#[allow(unused_braces)]
pub mod tmp_region;
