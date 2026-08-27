# Patches

Local changes to the `tools/verus` checkout, carried as patch files so a build is
always *an upstream commit plus a reviewable set of files*.

The changes live as a **commit in the vendored `tools/verus` checkout**
(`Add support for TypeId`), with upstream merged on top by
`cargo dv bootstrap --upgrade`. This file is the portable export of that commit —
the thing to hand to anyone reconstructing the toolchain from a stock checkout.

## Refreshing the patch

    cd tools/verus
    git diff origin/main HEAD > ../../patches/0001-verus-type-identity.patch

`origin/main..HEAD` is exactly our delta, because `HEAD` is a merge of our commit
and upstream. Check it against a stock checkout rather than trusting it:

    TMP=$(mktemp -d)
    git -C tools/verus worktree add -q --detach $TMP origin/main
    git -C $TMP apply --check ../../patches/0001-verus-type-identity.patch
    git -C tools/verus worktree remove --force $TMP

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

    cargo dv verify --targets ostd                      # 1521 verified, 0 errors
    cargo dv verify --targets ostd --features type_id   # 1525 verified, 0 errors

`--features` needs `dv` at `9543854` (#42) or later; the submodule now points at
`b4bc559`. If you ever hand-roll the `cargo-verus` command instead, note that it
rejects `--features` *after* `--target`, because it would otherwise be silently
ignored — `dv` has a regression test for exactly that
(`cargo_features_precede_target_and_verus_args`).

`dv` caches aggressively and `cargo clean -p ostd` cleans the **host** target, not
the verification one. To force a real re-run:

    cargo clean -p ostd -p vstd_extra --target x86_64-unknown-none

## Constructor ids are counted, not hashed

A per-context counter numbers user constructors `1, 2, 3, ...` as they are
emitted, so spec-side distinctness is injective by construction and there is no
hash of ours left to collide.

Hashing the type's path was implemented and committed instead (branch
`typeid-hash-ids`), on the reasoning that a counter "proves distinctness for
every pair, which is stronger than Rust guarantees". That reasoning does not
survive: a path hash and rustc's type-id hash are independent functions over
different domains, so they collide on different pairs. Under a runtime collision
the path hashes still differ, the spec still calls the two types distinct, and
the `assume_specification` in `vstd/std_specs/any.rs` is falsified exactly as it
would be under a counter. Hashing removes no failure mode and adds one — a
63-bit path collision, some 2^65 likelier than the runtime one.

What the counter costs instead is a *structural* assumption in place of a
probabilistic one: two emission passes over different or differently-ordered
datatype sets must never reach one context, or the context turns inconsistent
and every query in it passes vacuously. That is the sharper risk in practice —
silent, unbounded, and triggered by a plausible refactor rather than by a
2^-63 event. The invariant, the three properties currently holding it up, and
the one-line probe that would make a violation loud are documented at the tag
note in `vir/src/def.rs`. Read that before touching `datatype_to_air`.

## Emission inertness of `0001-verus-type-identity.patch`

**Half done.** The per-datatype tag axiom — the dominant cost, one quantified
axiom per reachable datatype — is now gated on `Ctx::uses_type_id`, a type-level
scan of the module's pruned krate for the `TypeTag` primitive
(`vir/src/traits.rs::krate_uses_type_id`). A module that never mentions type
identity gets none of them.

Still emitted unconditionally: the `TypeTag` sort, its declarations, the ~13
ground axioms and the 12 `dcr%tag` axioms. Gating those too is the remaining
work; it is the harder surgery, since those nodes are interleaved with the
box/unbox machinery inside a single `nodes_vec!` in `vir/src/prelude.rs`.

The gating stopped being optional when identity became decoration-sensitive
(`docs/verus-typeid-decoration.md`): folding decorations roughly doubles a
datatype tag, which cost two `ostd` proofs their rlimit. Inlining the pairing on
the hot path recovered one; gating recovered the other.

Until the rest lands, the patch may still perturb a proof that leans on an
unstated trigger — `patches/0001-ostd-...` is the worked example of repairing one.
