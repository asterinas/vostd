# Patches

Local changes to the `tools/verus` checkout, carried as patch files so a build is
always *an upstream commit plus a reviewable set of files*.

Seven patches, all against **`asterinas/verus`, branch `main`, commit
`025d77f2`** — which pins **Rust 1.100.0**, so `rust-toolchain.toml` moved with
it (1.99.1 → 1.100.0).

Moved there from `085772b8` on 2026-11-18, 46 commits of upstream. What that
cost is recorded under *Rebasing onto `025d77f2`* below: one rebase conflict,
two upstream API removals, and two downstream specs that upstream had grown
itself.

## Rebasing onto `025d77f2`

Done 2026-11-18, 46 upstream commits. Of the 35 files the stack touches, 21 had
moved. The textual rebase took **one** conflict, and the build then found two
more breaks that no merge could have flagged -- which is the shape to expect: a
clean rebase of this stack is not evidence it compiles.

- **`rust_verify_test/tests/traits_dyn.rs`** -- a pure append collision. #3466
  added 182 lines of dyn-compatibility tests at the end of the file, where
  `0002` appends its own; both sides' last test block shares the file's closing
  brace. Resolution is to keep both, upstream's first.
- **`vir/src/modes.rs`** -- #3483 deleted `Ctxt::check_ghost_blocks` (ghost
  blocks are now always checked), which `0001` and `0007` each read in a guard
  (`ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec`). Upstream
  rewrote its own sites by dropping the flag; ours do the same. Fixed in each
  patch separately so every prefix of the stack still builds.
- **`rust_verify/src/trait_conflicts.rs`** -- #3470 (Rust 1.100) removed
  `gen_generics`'s fourth parameter, the `is_impl: Option<&TraitImpl>` hack for
  `Option`'s `Clone` impl. `0002` passed `None` there, so deleting the argument
  is exactly behaviour-preserving.

`0003` survives, and is still worth sending upstream: #3466 *looks* like it
fixes the same bug -- it threads `merged_traits` into
`set_krate_dyn_compatibility` -- but `finish_dyn_compatability_checks`, the
deferred check `0003` repairs, still builds its map from `krate.traits` alone.
Verified against `025d77f2`, not assumed.

Two downstream specs also had to move, because upstream grew its own versions of
things `vostd` was carrying locally. Both are in *What the sync cost downstream*
below.

### Earlier moves

Both were refreshed against `085772b8` on 2026-11-11, from `b63c76a4`. Three
things needed hand-resolving, recorded here because they will recur on the next
move:

- `vir/src/context.rs` grew observer fields (`observer`, `air_observer`,
  `query_result_observer`) at the same slot the patch adds `type_tag_hashes` to,
  both in the struct and in its initializer. Keep both sides; this is the same
  alphabetical-slot collision `vstd/std_specs/mod.rs` has.
- `PathX::segments` is now `Arc<Vec<Segment>>` over a structured `ast::Segment`
  enum, no longer `Arc<Vec<Arc<String>>>`. Two sites cared: `def.rs`'s
  `typetag_type` now just defers to `internal_path` like its neighbours, and
  `sst_to_air.rs`'s `path_type_tag_id` had to grow a per-variant encoding (see
  *Constructor ids are hashed* below — getting this wrong is unsound, not just
  broken).
- `rust_verify/src/trait_conflicts.rs` no longer has `Arc` in scope, so `0002`
  carries `use std::sync::Arc;` itself.

Earlier refreshes: `0001` against `b63c76a4` on 2026-10-21, from `fec4c33a`,
where `Ctx` lost its `pub debug: bool` field upstream (so the patch must no
longer re-add it — it was only ever context) and `vir/src/recursive_types.rs`
grew two `match`es over `TypX` needing a `Primitive::TypeTag` arm, grouped with
the other simple primitives in both.

All seven are required unconditionally now that the gates are gone; the last
column says what each one buys rather than which feature used to select it.

| Patch | Supplies | Needed for |
|---|---|---|
| `0001-verus-type-identity.patch` | the `TypeTag` encoding and **both halves of identity** — `type_id::<T>()` for a type, `type_id_of(x)` for a value, related by A1 — plus `vstd/std_specs/any.rs` | `recorded_meta_id` and tagged storage; the erased identity `dyn_meta` and `axiom_untyped_recorded_by_id` report; both sides of the downcast guard |
| `0002-verus-dyn-supertrait-impls.patch` | supertrait impls for `dyn` types in the trait-conflict checker, transitively and substituted per hop | discharging `dyn T: U`, which `USegment` needs, at any depth |
| `0003-verus-dyn-imported-traits.patch` | lets the deferred dyn-compatibility check see imported crates' traits | any `dyn` of a trait declared in another crate |
| `0004-verus-type-id-reject-dyn.patch` | `type_id` of a trait object type is an error, not a tag nothing relates | keeping identity honest where the encoding cannot distinguish |
| `0005-verus-dyn-reject-diagnostics.patch` | name which `dyn` feature is unsupported, and why | diagnostics only |
| `0006-verus-dyn-spec-fn-generic.patch` | a `dyn T` value's spec fns relate to the erased type generically, and through a subtrait object | erasure facts for a generic `Self`; retires the per-impl obligations |
| `0007-verus-any-surface.patch` | `core::any::Any` declared with no methods, so `dyn Any` is a legal type; `is`, `dyn_value` and the downcasts specified | `AnyFrameMeta: Any` and the downcast guard, as upstream writes them |

All seven apply with a plain `git apply` to a pristine checkout of that commit,
in order, and together reproduce the tree the counts below were measured
against.

`0001` carries **both halves of identity**, because they are one model and a
patch with only the static half gives a caller nothing to compare against.
`type_id::<T>()` is a function of the type -- enough on its own for
`vstd_extra`'s tagged storage, which records what a byte buffer holds -- while
`type_id_of(x)` is the identity of the type the *value* has, which for a trait
object is the type erased into it, and which is the question a downcast asks.
Two axioms carry the second, and the first of them is what joins the halves: a sized value is its own type (guarded on the decoration
being sized, so it never fires on a trait object), and erasure is the identity
on runtime type -- the latter stated by asking the *source* value the same
question rather than answering it, which is what makes it right for a supertrait
upcast, where the source is itself a trait object. The payoff is that
`type_id_of(v as &dyn T) == type_id::<F>()` holds for a *generic* `F: T`, which
is the fact `AnyFrameMeta::meta_id_correct` and its per-impl obligations existed
to simulate by hand, and which is why they could be deleted.

`0002` covers the supertraits **transitively**, which is not optional for any
hierarchy deeper than one hop. Each emitted `impl U for Dyn<n, ..>` is checked
by rustc against `U`'s own declaration, which carries `where Self: V` for every
supertrait `V` of `U`, so a missing second hop is a *hard error* -- `the trait
bound Dyn<n, ()>: V is not satisfied`, reported against the subtrait's
declaration -- and not the incompleteness the first version of this patch
claimed. `trait R: Q`, `Q: P` plus a `dyn R` anywhere is enough to hit it. The
SMT side needed nothing: `tr_bound%R(DYN%R)` chains through
`trait_bound_axioms` on its own, so only the generated trait-conflict program
lagged. (The transitive half was carried separately as a `0004` for a day; it is
folded in here, since it is the same emission finished rather than a second
change.)

Two corrections to the one-hop version's comments, both now fixed in the code:

- The trait map it consults is built from the krate the conflict checker is
  handed, which is the **merged** krate (`verifier.rs` sets
  `self.vir_crate = merged_crate`), so it already spans imported crates. An
  unknown path there means pruned-out or never-declared, not foreign.
- Supertraits with associated types are still skipped, but that case is
  unreachable rather than merely incomplete: rustc demands a projection
  (`dyn T<X = ..>`) for such a hierarchy, and `mid_ty_to_vir` rejects that
  first.

`0003` is a fix for an upstream bug rather than an extension, and is worth
sending upstream. `well_formed::check_one_typ` admits a `dyn T` whenever `T` is
in the *merged* trait map, which spans imported crates, but it defers the
dyn-compatibility check (the trait's `dyn_compatible` is not yet computed at
that point); `finish_dyn_compatability_checks` then rebuilt its map from
`krate.traits` alone, so a `dyn` of a trait declared in *another* crate was
accepted by the first check and rejected by the second as "not declared to
Verus". Nothing in-tree hit it because a crate's own `dyn` traits are in
`krate.traits`; `ostd` hits it because its `dyn Any` is a `dyn` of a trait
declared *elsewhere* -- `core::any::Any`, declared to Verus by `ExAny` in
`vstd` -- which is still the case after `0007`, with `vstd` now in the role
`vstd_extra` held before it. The symptom when it was measured, against the
`to_any`/`vstd_extra::typing::types::Any` shape that `0007` retired, was five
such errors in the `type_id` shape -- `frame/meta.rs`, `frame/mod.rs`,
`frame/linked_list.rs`, `page_table/node/mod.rs` and
`specs/mm/frame/meta_owners.rs` -- while the declaring crate itself built, since
a `dyn Any` inside it is fine.
The fix feeds the imported crates into that second map, imported first so the
crate being verified still wins a collision. Upstream's own `traits_dyn`,
`traits` and `safe_api` suites (297 tests) pass with it.

`0004` closes the one place where `type_id` had a tag but no law. Verus models a
trait object type by its trait path and type arguments, which cannot tell `dyn A`
from `dyn B`, so neither the equality nor the disequality of their tags was
provable and a caller got an unexplained `assertion failed` wherever the identity
was finally compared. The alternative was an axiom giving each `dyn` type a
hashed tag like a datatype's; it was dropped because nothing needs it -- every
in-tree `type_id`/`recorded_id` instantiation is a concrete sized type or a type
parameter, and `downcast_ref<T: Any>` carries an implicit `T: Sized`, so downcast
targets are never trait object types. The identity of the type *inside* a trait
object is a different question and is the one the downcast needs; see
`ANY-SUPPORT-PLAN.md` section 4.1a.

The check is syntactic and fires for a `dyn` type anywhere in the argument
(`dyn A`, `Box<dyn A>`, `Wrap<dyn A>`), because a tag folds in the tags of its
arguments. It withdraws one fact that used to hold -- `type_id::<dyn A>() !=
type_id::<C>()`, free from `$dyn` being its own decoration -- and leaves `?Sized`
type parameters alone, which is both why `recorded_id::<T>()` still works and the
limit of the check: it cannot see a parameter later instantiated at a `dyn` type.

`0005` is diagnostics only. `dyn T + Send` and `dyn T<X = u8>` both used to
report "dyn with more than one trait" -- misleading for the first, wrong for the
second, and a message that never described a reachable case, since Rust rejects
two non-auto traits in a `dyn` type itself. Both stay rejected; the error now
names which feature is missing and that `TypX::Dyn` has nowhere to put it.

`0006` replaces the per-impl dyn spec-fn axiom's *reach*, not the axiom: the
original fires only once an impl is resolved, so a caller holding `F: T` for a
type parameter learned nothing about an `F` it had erased, and an inherited
supertrait spec fn observed through a subtrait object connected to nothing at
all. Both now follow from one axiom family quantified over the erased type under
the trait's bound. That is what lets a client stop declaring a spec fn plus a
per-impl obligation to recover by hand what the vtable already does -- the
`meta_id`/`meta_id_correct` shape `ostd` carried until this, and no longer does.
The per-impl axiom is still emitted;
it is an instance of the new one, kept until the comparison is measured.

`0007` makes `core::any::Any` usable, by declaring it to Verus with **no
methods**. The declaration is what makes `dyn Any` a legal type; the omission is
what keeps it sound, since `core`'s blanket impl reads `TypeId::of::<Self>()`
and at `Self = dyn Any` that is the trait object type's own identity rather than
the erased one -- rustc may pick either reading (rust#57893). The executable
answer comes from `<dyn Any>::is`, an inherent method of `dyn Any`, where no
second reading exists. Two places in the #57893 machinery had to be relaxed for
a trait with no methods and no associated types, where a blanket impl and the
object impl have nothing to resolve differently: the dyn-compatibility check,
and the conflict checker's own `dyn T: T` emission. Both exemptions are scoped by `is_tolerated_blanket_trait` to
`core::any::Any` and still enforce the member-less condition, which is the
actual reason: the general rule would also make `traits_dyn`'s
`dyn_rust_blanket_unsoundness` pass, and relaxing a soundness regression test
wants its own review.

With that, `AnyFrameMeta` is upstream's declaration again and the downcast guard
is upstream's expression. `0007` also carries `dyn_value`, the spec primitive
that lets a downcast name the value it returns -- the coercion is the identity
on the value, so reading it back at the type it was written at returns it -- and
with it `<dyn Any>::downcast_ref` and `Box<dyn Any, A>::downcast`, both
specified and verified end to end. `downcast_mut` is left out: a write through
the extracted reference has to be a write to the erased value, which needs the
converse axiom.

**The lineage is `asterinas/verus`, not `verus-lang/verus`.** This is the single
most expensive mistake available here. The two forks have diverged, and a
toolchain built from `verus-lang` lacks the `bitvec`/`wyz` specifications `ostd`
now depends on; the symptom is seven *is not supported* / *does not recognize
associated type* errors while compiling **`vstd_extra`**, which looks like a
broken `Cargo.toml` in this workspace and is not. `cargo dv bootstrap` fetches
the right one; prefer it over any hand-managed checkout.

The reference checkout is `../verus`. Three branches there matter:

- **`any-support`** is where development happens as of 2026-11-18: all seven
  patches as seven commits, one per patch and in the same order, based on
  **`025d77f2`** -- the `asterinas/verus` commit `tools/verus` sits on. Its tree
  is byte-identical, across all 35 files, to the `tools/verus` tree the counts
  below were measured against, and so is the tree the patches produce from a
  pristine checkout -- both are checked the same way. `0003` stays
  cherry-pickable on its own for a `verus-lang` PR: it touches `query.rs` and
  `well_formed.rs`, which nothing else in the stack does, and it still applies
  cleanly to `verus-lang` `main`.
- `backup/any-support-085772b8` is the pre-rebase stack at `b7a76357c`, kept
  because it is the only record of the 7 commits as they read against the old
  base.
- `typeid-and-dyn` is the older reference, on the `verus-lang` lineage, carrying
  type identity plus the supertrait work as they stood before this.

Fetch `asterinas/verus` over **HTTPS**, not `origin`: `../verus`'s `origin` is
`git@github.com:asterinas/verus.git`, the SSH key is not always available, and
there is no `origin/main` ref to fall back on --
`git fetch https://github.com/asterinas/verus.git main` is what works. Same for
`verus-lang`, which is the `upstream` remote.

`tools/verus` remains the toolchain this workspace verifies against, and still
holds the changes as uncommitted working-tree edits on top of `025d77f2`.
`../verus`'s own checkout now sits on `backup/any-support-085772b8`, since
`any-support` is checked out in the scratch worktree the rebase was built and
tested in; `git -C ../verus switch any-support` needs that worktree removed
first.

**Its two internal design docs are gone.**
`source/docs/internal/type-identity-emission.md` and `type-identity-prelude.md`
were the authoritative account of the encoding, were never committed (this file
used to warn about exactly that), and are now absent from `../verus` — whose
tree is clean, with a single stash holding only `trait_conflicts.rs` — and from
`tools/verus`. Nothing in the tree cites them any more — the one file that did,
`verified_libs/vstd_extra/src/typing/types.rs`, was deleted with the feature
gates — so the sections below and `ANY-SUPPORT-PLAN.md` are the account of
record until they are rewritten.

## Refreshing a patch

Regenerate against the **bootstrapped `tools/verus`** or against `any-support`,
which sits on the same commit. Do *not* diff against `../verus`'s **older**
branches, which carry
an earlier generation of this work: that is where the three-way merge and the
hand-resolved `vstd/std_specs/mod.rs` conflict came from, not from the lineage
as such.

### The stack is lineage-neutral

Measured twice on 2026-11-18, before and after the move to `025d77f2`, and
worth re-measuring whenever either fork moves: the patches are **not** specific
to `asterinas`. All seven apply in order with a plain `git apply`, no three-way
merge, to `verus-lang/verus` `main` -- at `86e7f117f` from the old base, and
again at `a95764f23` from the new one, where the `asterinas` base is 3 commits
ahead and 7 behind.

Measure this with a **sequential** apply and plain `git apply`. Two traps, both
of which produced a false "all seven conflict" here: these patch files carry no
`index` lines, so `git apply --3way` cannot find its blobs and degrades to
direct application; and `0004`, `0006` and `0007` genuinely fail *standalone*
because their context is text an earlier patch adds, which says nothing about
the stack. In zsh, also beware `P=dir/000$k-*.patch` -- assignment does not
glob, and the resulting "can't open patch" reads exactly like a conflict.

From the old base the reason was structural: of the **35 files the stack
touches, none differed between the two bases.** The forks shared merge-base
`28029acb4` and diverged in only eight files, which the patches did not go
near:

| file | which fork is ahead |
| --- | --- |
| `.github/workflows/promote-update-test.yml`, `upstream-sync.yml` | `asterinas` CI only |
| `rust_verify/src/rust_to_vir_func.rs`, `rust_to_vir_impl.rs`, `vir/src/modes.rs`, `rust_verify_test/tests/external_fn_specification.rs` | `asterinas` — projection normalization before filtering external trait impls |
| `vstd/bytes.rs`, `rust_verify_test/tests/std.rs` | `verus-lang` — `from_le_bytes` |

It builds and passes its tests there, too -- measured on the `86e7f117f` base.
On a `verus-lang` worktree with all seven applied, `cargo build --release --features singular` succeeds, `vstd`
itself comes out **2228 verified, 0 errors**, and eleven suites are green --
**667 passed, 0 failed**, 5 ignored:

| suite | passed | suite | passed |
| --- | --- | --- | --- |
| `type_id` | 29 | `safe_api` | 35 |
| `any` | 10 | `traits_modules` | 37 |
| `traits_dyn` | 52 | `std` | 65 |
| `traits` | 223 | `external_fn_specification` | 82 |
| `external_traits` | 43 | `erase` | 6 |
| `marker_traits` | 85 | | |

The first eight counts are identical to the `asterinas` build's. `std` and
`external_fn_specification` are the two suites whose *files* differ between the
forks, so their counts are base-dependent by construction and are not
comparable across lineages.

These suites run in seconds, which looks wrong and is not: the cases are tiny
crates that mostly do not import `vstd`. Confirmed by negative control rather
than by assumption -- `VERUS_Z3_PATH=/nonexistent/z3` turns a passing case
straight into a failure, so the harness is really spawning the built
`rust_verify` and really calling z3.

What stays lineage-bound is **verifying `vostd`**, which is a separate question
from whether the patches land: a `verus-lang` `vstd` lacks the `bitvec`/`wyz`
specifications `ostd` depends on, which is the seven-error symptom described
above. The patches are portable; the `vstd` this workspace verifies against is
not.

With a stack this size, reverse-applying one patch to isolate another stops
being workable -- several of them touch the same files, and two of them append
to the same test file. **Replay instead.** Apply the whole stack in order in a
pristine worktree, snapshot the files any patch touches after each step, and
emit each patch as the diff between consecutive snapshots:

    W=$(mktemp -d)/w
    git -C tools/verus worktree add -q --detach $W 025d77f2
    # for k in 1..7: snapshot, git -C $W apply patches/000k-*.patch, snapshot
    # patch k = diff(snapshot k-1, snapshot k), per file

Reordering or merging patches works the same way, with one wrinkle: where two
patches **append** to one file, the later one's context is the earlier one's
added lines, so a reorder conflicts there and nowhere else. Split that file's
final content into its per-patch blocks by hand (the test files have banner
comments marking the boundaries), hand each block to the right step, and let the
replay rebuild the rest. Merging the value-identity patch into `0001` needed
exactly that, in exactly one file.

**Pass absolute paths.** `git -C <dir> apply <relative>` resolves the patch
relative to `<dir>`, so a repo-relative path silently fails to open.

Then check the result rather than trusting it, and check the *whole tree*, not
just the files you think you touched:

    W=$(mktemp -d)/w
    git -C tools/verus worktree add -q --detach $W 025d77f2
    for p in patches/0*.patch; do git -C $W apply $PWD/$p || echo "FAILED $p"; done
    diff -rq $W/source tools/verus/source --exclude=target --exclude=target-verus \
        --exclude=.verus-log --exclude=z3 --exclude=cvc5 | grep -v Cargo.lock
    git -C tools/verus worktree remove --force $W

Silence from that `diff` is the only evidence that matters: the patches
reproduce the tree the counts were measured against. Run it before every commit
that touches `tools/verus`. These patches had
silently gone stale once across a `TypeId` -> `TypeIdSpec` rename, and a
regenerated one had silently dropped two files that were untracked at the time.

## What the sync cost downstream

Upstream grew its own versions of two things `vostd` was carrying, and both
needed a downstream edit. Neither touched executable code or a proof body.

**`verified_libs/vstd_extra/src/external/bits.rs` -- a duplicate
specification.** #3513 added `count_ones` to `vstd`, so the local
`assume_specification[ u64::count_ones ]` became a hard
*duplicate specification for `core::num::impl&%9::count_ones`* error, which
fails the build rather than the proof. The local `u64_set_bits` was a recursive
definition over `u64_bit_is_set`; it is now `w.count_ones() as int`, and
`lemma_u64_set_bits_nonzero` is discharged by `broadcast use
axiom_u64_count_ones`, whose two clauses (`<= 64`, and `== 0` iff the word is
zero) are exactly what the local lemma proved. That deleted ~60 lines of
bit-vector proof and 9 verification conditions. The lemma gained one clause,
`w.count_ones() == u64_set_bits(w)`, which is what the deleted
`assume_specification` used to supply to callers; `u64_set_bits` stays `closed`,
so the clause is proved inside the module where the body is visible.

**`ostd/src/util/range_alloc.rs` -- a new hypothesis on `BTreeMap::iter`.**
#3494 strengthened the guard on `iter`'s postcondition from
`key_obeys_cmp_spec::<Key>()` to `key_obeys_cmp_spec::<Key>() &&
btree_map_wf(m)`, so a caller now learns nothing about the iterator without
`btree_map_wf`. Five errors in two `for (key, value) in freelist.iter()` loops,
all of them downstream of `it.seq().unref().to_set() == freelist@.kv_pairs()`
failing before the loop.

`btree_map_wf` is uninterpreted: `BTreeMap::new` establishes it and `insert` and
`remove` preserve it, so it has to be *carried*, and carried at the concrete
level -- the view does not determine it. Four conjuncts, no proof bodies:

- `ResourceInvariant::inv`'s `Sum::Right` branch gains
  `btree_map_wf(&freelist->0)`. This is the one that matters; the lock invariant
  takes the concrete `Option<BTreeMap<..>>`, so the predicate is expressible
  there at all.
- `get_freelist_guard`'s `ensures` gains `btree_map_wf(&freelist)`. Callers see
  only what that contract spells out, and it was view-level
  (`concrete_freelist_wf(self@, freelist@)`) -- which is why adding the fact to
  `inv` alone left the loops still failing.
- the two loop invariants gain `btree_map_wf(freelist)`.

## Applying to a fresh checkout

    git -C tools/verus apply $PWD/patches/0001-verus-type-identity.patch
    git -C tools/verus apply $PWD/patches/0002-verus-dyn-supertrait-impls.patch
    git -C tools/verus apply $PWD/patches/0003-verus-dyn-imported-traits.patch
    git -C tools/verus apply $PWD/patches/0004-verus-type-id-reject-dyn.patch
    git -C tools/verus apply $PWD/patches/0005-verus-dyn-reject-diagnostics.patch
    git -C tools/verus apply $PWD/patches/0006-verus-dyn-spec-fn-generic.patch
    git -C tools/verus apply $PWD/patches/0007-verus-any-surface.patch

Then rebuild — both steps, in `tools/verus/source`:

    cargo build --release --features singular
    cargo run --release -p cargo-verus -- build --release --manifest-path vstd/Cargo.toml

The second is not optional: rebuilding `rust_verify` invalidates the vstd
artifacts, and the symptom is `can't find crate for vstd` in every test.

Then run the tests as a **separate command**. Chaining them --
`cargo build ... && cargo test ...` -- lets the harness start while the build is
still replacing `target-verus/release/rust_verify`, and the run comes back with a
scattered set of failures (18 of `traits_dyn`'s 44, all `can't find crate for
vstd`) that look like a regression and are not: the same suite passed before and
after. The harness has a `wait_exists` delay for exactly this race and it is not
always enough. `source/.cargo/config.toml` is what puts the binaries there --
`target-dir = "target-verus"`, plus `VERUS_IN_VARGO=1`, which is why `cargo test`
works here at all without `vargo`.

Unrelated: `tools/patches/verus-irc11*.patch` are driven by
`tools/bootstrap-verus-irc11.sh` and `.github/workflows/ci-irc11.yml`.

## Downstream usage is unconditional

It used to be opt-in: `vstd_extra/type_id` gated the whole `typing::` module,
`ostd/type_id` gated the erased-metadata downcast, and `ostd/dyn_supertrait`
gated the `USegment` conversion, so the workspace still built and verified
against a stock Verus. **All three features are retired as of 2026-11-18.**

Two things ended them. `AnyFrameMeta: Any` is part of the trait's declaration
and `#[cfg]` is not honoured inside `verus!`, so the supertrait cannot be gated
-- the ungated shape needs a toolchain with `dyn Any` whether or not anything
else is enabled. And the gated code stopped being exotic: with `type_id_of` and
the `Any` surface in the toolchain, what the gates protected is just how the
metadata system is written.

So there is one shape now, and it is the maximal one: the ungated build verifies
everything the fully-gated build used to, at the same count. A stale `-F
type_id` fails loudly rather than silently -- `none of the selected packages
contains this feature: type_id`.

`irc11` is untouched; it gates a different toolchain (`tools/patches/verus-irc11*`)
and still follows the opt-in pattern.

Two notes from the gated era that still matter:

- `0002`/`0004` emit supertrait impls for **every** `dyn` trait in the crate, so
  they were never inert with respect to the `dyn_supertrait` gate -- the gate
  controlled which vostd code *relied* on those impls, not whether they were
  emitted. Retiring it changes nothing about the emission.
- `AnyFrameMeta`'s `'static` bound used to be written explicitly, because `Any`
  -- which supplies it upstream -- could not be modelled. The supertrait is back,
  so the bound comes from it again, as upstream has it.

Verify:

    cargo dv verify -p ostd                                 # 1567 verified, 0 errors

Measured 2026-11-18 against `asterinas/verus` `main` at `025d77f2` with all seven
patches applied, on `typeid-rework` at `b4a530050`, from a cleaned verification
target (see the caching note below -- anything less is a cache hit), and again
after `make fmt`. `vstd_extra` is at **764**, and the `vstd` that ships with the
toolchain builds at **2338** verified, 0 errors.

Upstream's own suites are green on this base too -- eleven of them,
**700 passed, 0 failed**, 5 ignored: `type_id` 29, `any` 10, `traits_dyn` 57,
`traits` 230, `external_traits` 52, `marker_traits` 85, `safe_api` 35,
`traits_modules` 37, `std` 77, `external_fn_specification` 82, `erase` 6. Four
of those counts rose with the move (upstream's own new cases), `traits_dyn`
among them -- #3466's dyn-compatibility tests pass alongside `0007`'s narrowed
`core::any::Any` exemption, which is the pairing most at risk here.

`ostd` is unchanged at 1567 across the move to `025d77f2`, which is the point:
46 commits of upstream and a rustc bump cost two downstream specs and no proofs.
`vstd_extra` fell 773 -> 764 because the duplicate `count_ones` specification
went away with its recursive definition, and the toolchain's `vstd` rose
2228 -> 2338 on upstream's own new specs, neither of which is a change in this
work.

The number moved twice on the way here, both times downward and both times
because a workaround went away: the `type_id_of` migration deleted the three
`meta_id_correct` obligations (1573 -> 1570 in what was then the maximal shape)
and the `Any` surface deleted the three `to_any` impls (1570 -> 1567). The
retired gates are why there is one figure instead of three: the ungated build
now verifies what only `-F type_id,dyn_supertrait` used to.

Earlier figures are triples, one per feature shape, and are not comparable with
each other either -- each is separated from the next by an upstream move:
1563/1564/1567 on 2026-11-18 before the gates were retired; 1496/1503/1506 with
`vstd` at 2059, 2026-10-21 at `b63c76a4`; and 1510/1517/1518, 2026-10-01 at
`fec4c33a`.

A proof lost its rlimit to this work, and the remedy is worth knowing before the
next toolchain move. `Segment::<M>::drop`'s loop exceeded it once the `Any`
support's declarations were in scope -- in the **default** shape only, where
`dyn Any` becomes reachable, while the then-gated shapes passed. Nothing was wrong
with the proof: merely declaring a sort and a few axioms moves Z3's heuristics,
and that loop sits near its limit. `#[verifier::spinoff_prover]` recovered it
with no rlimit increase, which is what `PageTableOwner::pt_inv_unroll` needed
when type identity first landed. Expect one or two of these per toolchain move,
and reach for `spinoff_prover` before touching rlimits.

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
    cargo dv verify -p ostd
    rm tools/verus && mv tools/verus.bak tools/verus

`--features` needs `dv` at `9543854` (#42) or later; the submodule now points at
`efb1b60` (#49), which renamed `--targets` to `-p`/`--package` and took
`--target` for the CPU triple. If you ever hand-roll the `cargo-verus` command instead, note that it
rejects `--features` *after* `--target`, because it would otherwise be silently
ignored — `dv` has a regression test for exactly that
(`cargo_features_precede_target_and_verus_args`).

`dv` caches aggressively and `cargo clean -p ostd` cleans the **host** target, not
the verification one. The package-scoped clean this file used to recommend,

    cargo clean -p ostd -p vstd_extra --target x86_64-unknown-none   # NOT enough

is *not* enough either, measured 2026-11-17 after rebuilding `rust_verify`: it
removed 108 files / 240MiB and the next `cargo dv verify -p ostd` still printed
no `verification results::` line at all, finishing in 65s (all of it the rustc
build) and then 0.35s on the following run. `touch`ing `ostd/src/lib.rs` did not
dislodge it either. What forces a real re-run is cleaning the whole verification
target:

    cargo clean --target x86_64-unknown-none

That re-verifies the dependency crates too (`vstd` 1968, `vstd_extra` 777, ...),
which is the point: the per-crate lines are the evidence the run happened.
**A pass with no `verification results::` line is not a pass**, it is a cache
hit -- the same trap as reading these runs with `head` instead of `tail`.

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
- **Every part of a segment is in the component**, not just its name. A segment
  is an `ast::Segment`, so each renders as a kind tag (`V`/`T`/`C`/`I`/`F`/`O`/
  `L`/`A`), its disambiguator, and — for `V` and `T` — a length-prefixed
  identifier. Dropping the kind would identify `V("foo", 0)` with `T("foo", 0)`
  and dropping the disambiguator would identify `V("foo", 0)` with
  `V("foo", 1)`, either of which makes `type_id` equal for two types rustc keeps
  distinct. Before `085772b8` segments were plain strings and the name alone
  sufficed.
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
other. Expect the patch to perturb proofs that lean on an unstated trigger.

The `b63c76a4` refresh cost one: `PageTableOwner::pt_inv_unroll` in
`specs/mm/page_table/owners.rs`, which verifies on `main` and, with the patch
applied, failed with every sub-assertion of its postcondition proved and the
whole unproved. `#[verifier::spinoff_prover]` recovered it, with no `rlimit`
increase. That is the pattern to expect, and `--expand-errors` is the
diagnostic: a failure with no `✘` beneath it is this, not a missing fact.
