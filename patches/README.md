# Patches

Local changes to the `tools/verus` checkout, carried as patch files so a build is
always *an upstream commit plus a reviewable set of files*.

The changes live as a **single commit on the `typeid-hash-ids` branch** of our
Verus fork — `9b3934b9`, *Encode unique `TypeTag` for each type*, plus three
follow-ups — rebased onto upstream rather than merged with it. This file is the portable export of that
commit: the thing to hand to anyone reconstructing the toolchain from a stock
checkout.

The reference checkout is `../verus`, on `typeid-hash-ids`. Its internal design
docs — `source/docs/internal/type-identity-emission.md` and
`type-identity-prelude.md` — are the authoritative account of the encoding and
supersede the summaries here. **Both are currently untracked in that checkout**,
so a regeneration will not carry them; commit them before relying on the export.

## Refreshing the patch

    cd ../verus                       # on branch typeid-hash-ids
    git diff upstream/1.98.0 HEAD > ../vostd/patches/0001-verus-type-identity.patch

**The base is `upstream/1.98.0`, not `upstream/main` and not `origin/main`.**
`rust_verify` is a rustc driver and has to match the channel of the crate it
verifies; `ostd` moved to Rust 1.98.0 in asterinas #745, and upstream carries
that on a long-running `1.98.0` branch that periodically merges `main`. Rebasing
there costs whatever `main` has landed since its last merge — at the time of
writing, ten commits, including the array/slice `decreases` work (#2888, #2890).
The fork's `origin` has no `main` at all, only `typeid-hash-ids` and
`typeid-counter-ids`, so the old spelling of this command failed outright.
Check the result against a stock checkout rather than trusting it:

    TMP=$(mktemp -d)
    git -C ../verus worktree add -q --detach $TMP upstream/1.98.0
    git -C $TMP apply --check patches/0001-verus-type-identity.patch
    git -C ../verus worktree remove --force $TMP

Run that before every commit that touches `tools/verus`. This patch had silently
gone stale once across a `TypeId` -> `TypeIdSpec` rename, and a regenerated one
had silently dropped two files that were untracked at the time.

## Applying to a fresh checkout

    git -C tools/verus apply patches/0001-verus-type-identity.patch

Then rebuild — both steps, in `tools/verus/source`:

    cargo build --release --features singular
    cargo run --release -p cargo-verus -- build --release --manifest-path vstd/Cargo.toml

The second is not optional: rebuilding `rust_verify` invalidates the vstd
artifacts, and the symptom is `can't find crate for vstd` in every test.

Unrelated: `tools/patches/verus-irc11*.patch` are driven by
`tools/bootstrap-verus-irc11.sh` and `.github/workflows/ci-irc11.yml`.

## Downstream usage is feature-gated

The patch changes the toolchain; the code that *uses* it is opt-in, so this
workspace still builds and verifies against a stock Verus.

| Crate | Feature | Gates |
|---|---|---|
| `vstd_extra` | `type_id` | the whole `typing::` module |
| `ostd` | `type_id` (implies `vstd_extra/type_id`) | `AnyFrameMeta::{meta_id, to_any}`, `Frame::<dyn AnyFrameMeta>::{meta_type_id, dyn_meta}`, both `TryFrom` impls, and the identity clause on `into_dyn` |

Off by default, following the `irc11` precedent. `into_dyn` is the one item that
exists either way — it has real callers — so it is split in two, differing only
in whether the postcondition pins the erased frame's identity. Runtime behaviour
is identical.

Verify both shapes:

    cargo dv verify --targets ostd                      # 1514 verified, 0 errors
    cargo dv verify --targets ostd --features type_id   # 1521 verified, 0 errors

Measured 2026-09-05 against `typeid-hash-ids` rebased onto `upstream/1.98.0`.
`vstd_extra` goes 567 -> 583 across the same pair, and `vstd` itself builds at
2045 verified, 0 errors.

**`tools/verus` has to *be* the patched checkout.** Setting `CARGO_VERUS_PATH` is
not enough: `dv`'s `executable::locate` tries its hints *before* the environment,
so `tools/verus/source/target-verus/release` always wins. And even overriding the
binary is not enough, because the workspace takes `vstd` as a **path dependency**
on `tools/verus/source/vstd` (root `Cargo.toml`) — so the vstd *source* is
compiled from there too, and a new `rust_verify` against an old vstd fails with
`external_trait_private_bound` on `slice`, `atomic` and `nonzero`. The directory
is gitignored, so the quickest way to verify against a checkout you have already
built is to swap it in:

    mv tools/verus tools/verus.bak
    ln -s /path/to/verus tools/verus
    cargo dv verify --targets ostd --features type_id
    rm tools/verus && mv tools/verus.bak tools/verus

`--features` needs `dv` at `9543854` (#42) or later; the submodule now points at
`6d6502d` (#45). If you ever hand-roll the `cargo-verus` command instead, note that it
rejects `--features` *after* `--target`, because it would otherwise be silently
ignored — `dv` has a regression test for exactly that
(`cargo_features_precede_target_and_verus_args`).

`dv` caches aggressively and `cargo clean -p ostd` cleans the **host** target, not
the verification one. To force a real re-run:

    cargo clean -p ostd -p vstd_extra --target x86_64-unknown-none

## Constructor ids are hashed, not counted

`sst_to_air::path_type_tag_id` hashes the datatype's path with SHA-512 and uses
the full digest as the constructor id. Three properties carry it:

- **The stable crate id, never the friendly name.** The hashed string spells a
  crate as `{ident}#{stable_id}`. `path_as_friendly_rust_name` renders it by
  name alone, so two semver-incompatible versions of one dependency — the
  ordinary case — render identically and collide on a single tag, making
  `type_id::<v1::Foo>() == type_id::<v2::Foo>()` provable for two types rustc
  keeps distinct.
- **Components are length-prefixed** (`{len}:{component}`), so the byte stream
  determines the component list uniquely and no segment can forge a separator.
- **Collisions are detected, not assumed.** Every id is checked against
  `ctx.type_tag_hashes`; a repeat for a different path panics rather than
  silently identifying two types.

A per-context counter numbering constructors `1, 2, 3, ...` was implemented on
branch `typeid-counter-ids` and rejected. It is unsound *here*: `type_id::<T>()`
denotes a real `core::any::TypeId`, whose runtime value is itself a hash, so
distinctness of two types is not guaranteed at runtime. A counter makes
`type_id::<A>() != type_id::<B>()` provable for every distinct pair — stronger
than Rust promises — and under a runtime collision the `PartialEq`
specification in `vstd/std_specs/any.rs` would be false. Hashing keeps our
model's collision behaviour in the same class as the thing it models.

## Emission inertness of `0001-verus-type-identity.patch`

**Abandoned, deliberately.** `Ctx::uses_type_id` gated the per-datatype tag
axiom — the dominant cost, one quantified axiom per reachable datatype — on a
scan of the module's pruned krate for the `TypeTag` primitive. It was removed in
`8954f62e`, *Drop emission gating, wasn't doing much*.

The gate only ever covered half the emission. The `TypeTag` sort, its
declarations, the ground axioms and the `dcr%tag` axioms were always
unconditional, interleaved with the box/unbox machinery inside a single
`nodes_vec!` in `vir/src/prelude.rs`, and gating those was the harder surgery
that never happened. So a module that never mentions type identity never got the
byte-identical prelude the gate was meant to buy — `type-identity-prelude.md`
still claims it does, which is now doubly wrong.

What remains is the trigger discipline, which is what actually makes the feature
inert: every axiom is patterned on a *tag application* — `TYPE%tag(...)`,
`dcr%tag(...)`, or a `has_type` over a boxed tag — and never on a bare type id or
constructor. Nothing in an ordinary query mentions `TYPE%tag`, so none of them
instantiate. The gate was an optimisation on top of that, never a correctness
requirement.

It still costs something. Merely declaring a sort and a few dozen axioms
perturbs Z3's heuristics, which is enough to move a proof sitting near its
rlimit — and identity is decoration-sensitive, so folding decorations roughly
doubles a datatype tag. That cost two `ostd` proofs their rlimit once before;
inlining the pairing on the hot path recovered one and the gate recovered the
other. Expect the patch to perturb proofs that lean on an unstated trigger;
`patches/0001-ostd-...` is the worked example of repairing one.
