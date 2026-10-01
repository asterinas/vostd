# Patches

Local changes to the `tools/verus` checkout, carried as patch files so a build is
always *an upstream commit plus a reviewable set of files*.

Two patches, both against **`asterinas/verus`, branch `main`, commit
`fec4c33a`** — the commit `cargo dv bootstrap --upgrade` lands on, which pins
Rust 1.98.1:

| Patch | Supplies | Needed by |
|---|---|---|
| `0001-verus-type-identity.patch` | `TypeTag` encoding, `type_id::<T>()`, `vstd/std_specs/any.rs` | `type_id` |
| `0002-verus-dyn-supertrait-impls.patch` | supertrait impls for `dyn` types in the trait-conflict checker | `dyn_supertrait` |

Both apply with a plain `git apply` to a pristine checkout of that commit, in
order, and together reproduce the tree the counts below were measured against.

**The lineage is `asterinas/verus`, not `verus-lang/verus`.** This is the single
most expensive mistake available here. The two forks have diverged, and a
toolchain built from `verus-lang` lacks the `bitvec`/`wyz` specifications `ostd`
now depends on; the symptom is seven *is not supported* / *does not recognize
associated type* errors while compiling **`vstd_extra`**, which looks like a
broken `Cargo.toml` in this workspace and is not. `cargo dv bootstrap` fetches
the right one; prefer it over any hand-managed checkout.

The reference checkout is `../verus`, on `typeid-and-dyn` (type identity plus the
supertrait work). Its internal design docs —
`source/docs/internal/type-identity-emission.md` and
`type-identity-prelude.md` — are the authoritative account of the encoding and
supersede the summaries here. **Both are currently untracked in that checkout**,
so a regeneration will not carry them; commit them before relying on the export.
Note that `../verus` is itself based on `verus-lang`, so it is a source for
*reading* the changes, not a base to regenerate against — see below.

## Refreshing a patch

Regenerate against the **bootstrapped `tools/verus`**, not against `../verus`:
the latter sits on the `verus-lang` lineage, so a diff taken there will not apply
here (it needed a three-way merge and a hand-resolved conflict in
`vstd/std_specs/mod.rs`, where both lineages add a module at the same
alphabetical slot). To re-split the pair from a tree that has both applied:

    P1=$PWD/patches/0001-verus-type-identity.patch
    P2=$PWD/patches/0002-verus-dyn-supertrait-impls.patch
    git -C tools/verus apply -R "$P2"        # leave only type identity
    git -C tools/verus add -A                # include new files
    git -C tools/verus diff HEAD --binary > "$P1"
    git -C tools/verus apply "$P2"           # put it back

**Pass absolute paths.** `git -C <dir> apply <relative>` resolves the patch
relative to `<dir>`, so a repo-relative path silently fails to open — and if you
ignore the exit status, the revert no-ops and the "split" patch quietly contains
both changes.

Check the result against a pristine checkout rather than trusting it:

    W=$(mktemp -d)/w
    git -C tools/verus worktree add -q --detach $W fec4c33a
    git -C $W apply --check patches/0001-verus-type-identity.patch
    git -C $W apply       patches/0001-verus-type-identity.patch
    git -C $W apply --check patches/0002-verus-dyn-supertrait-impls.patch
    git -C tools/verus worktree remove --force $W

Run that before every commit that touches `tools/verus`. These patches had
silently gone stale once across a `TypeId` -> `TypeIdSpec` rename, and a
regenerated one had silently dropped two files that were untracked at the time.

## Applying to a fresh checkout

    git -C tools/verus apply $PWD/patches/0001-verus-type-identity.patch
    git -C tools/verus apply $PWD/patches/0002-verus-dyn-supertrait-impls.patch

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
| `ostd` | `type_id` (implies `vstd_extra/type_id`) | `AnyFrameMeta::{meta_id, to_any}`, `Frame::<dyn AnyFrameMeta>::{meta_type_id, dyn_meta}`, and both `TryFrom` impls |
| `ostd` | `dyn_supertrait` | `axiom_segment_reparam` and the `From<Segment<M>> for USegment` conversion |

`dyn_supertrait` gates a **second** toolchain requirement, carried here as
`0002`. `USegment` is `Segment<dyn AnyUFrameMeta>`, so discharging `Segment`'s
`M: AnyFrameMeta` bound there needs `dyn AnyUFrameMeta: AnyFrameMeta` -- a
supertrait impl, which stock Verus does not derive for `dyn` types (it emits one
impl per `dyn T` and none for `T`'s supertraits). Without `0002` the symptom is
`the trait bound Dyn<2, ()>: T193_AnyFrameMeta is not satisfied`.

The emission in `0002` is deliberately incomplete rather than wrong: it skips
supertraits with associated types, and skips transitive supertraits, because
either would need substitution work it does not do. Both leave a bound
undischargeable; neither emits an unsound impl. It also skips supertraits whose
path is not declared in the crate being verified, since their associated types
cannot be inspected -- treating unknown as "has none" emitted an impl for a
trait that had them, surfacing far away as `Verus does not recognize associated
type ... of trait ...`.

Note that `0002` emits for **every** `dyn` trait in the crate, so it is not
inert with respect to the `dyn_supertrait` feature gate -- the gate controls
which vostd code *relies* on those impls, not whether they are emitted.

`AnyFrameMeta` carries an explicit `'static` bound. Upstream gets it from the
`Any` supertrait, which is commented out here because Verus cannot model `Any` --
and without it `is_::<M>` and the `&dyn Any` coercion in `Link<M>` fail to
compile with `E0310: the parameter type M may not live long enough`. The bound
sits on the trait rather than at the two use sites so every `M: AnyFrameMeta`
gets it for free; it is unconditional because `#[cfg]` is not honoured inside
`verus!`, and it costs the default shape nothing.

Off by default, following the `irc11` precedent. Nothing now needs splitting
across the gate: erasure is a single ungated `From<Frame<M>> for
Frame<dyn AnyFrameMeta>` whose spec is a struct literal, so identity preservation
falls out of it rather than needing a `type_id`-only postcondition. (This replaced
a pair of gated `into_dyn` methods; the counts below each dropped by one as a
result.)

Verify both shapes:

    cargo dv verify --targets ostd                                       # 1506 verified, 0 errors
    cargo dv verify --targets ostd --features type_id                    # 1513 verified, 0 errors
    cargo dv verify --targets ostd --features type_id,dyn_supertrait     # 1514 verified, 0 errors

Measured 2026-09-30 against `asterinas/verus` `main` at `fec4c33a` with both
patches applied; `vstd` itself builds at 2059 verified, 0 errors.

When reading these runs, grep with `tail`, not `head`. `dv` prints a
`verification results::` line per crate, and `ostd`'s comes last; `head -4` keeps
the dependency crates' successes and discards `ostd`'s own errors, which reads as
a pass. The `type_id` shape appeared to pass that way while in fact failing to
compile.

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
