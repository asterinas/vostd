# Patches

Local changes to the `tools/verus` checkout, carried as patch files so a build is
always *an upstream commit plus a reviewable set of files*.

**Five** patches applied and one parked beside them, all against
**`asterinas/verus`, branch `main`, commit
`025d77f2`** — which pins **Rust 1.100.0**, so `rust-toolchain.toml` moved with
it (1.99.1 → 1.100.0).

Moved there from `085772b8` on 2026-11-18, 46 commits of upstream. What that
cost is recorded under *Rebasing onto `025d77f2`* below: one rebase conflict,
two upstream API removals, and two downstream specs that upstream had grown
itself.

Seven until 2026-11-23, when `0004-verus-type-id-reject-dyn.patch` was folded
into the type-identity patch -- it only ever edited that patch's own code, so as
two patches they read as an addition and then its correction.

**The three `dyn` patches come first**, reordered the same day, so that type
identity lands fourth rather than first. They need nothing from it -- none of
the three so much as mentions `type_id`, `TypeId` or `TypeTag` -- and in this
order `0001`-`0003` are a self-contained prefix: the dyn-compatibility fixes,
which are the part worth sending to `verus-lang`, no longer sit behind the
largest patch in the stack. Neither change moves the tree: both the merged and
the reordered stack reproduce, byte for byte, the `tools/verus` tree the counts
below were measured against.

Six until `verus-dyn-spec-fn-generic.patch` lost its sequence number on
2026-11-23 and the `Any`-surface patch took the number it vacated. Dropping the
number de-applies a patch without discarding it: `dv` runs every
`NNNN-*.patch` here and skips the rest. Nothing downstream consumed it, measured
both ways -- see *`verus-dyn-spec-fn-generic` has no consumer downstream*. The
applied set is therefore `0001`-`0005`, and `0006` moved down to `0005` with
it.

That prefix was **built and tested**, not just inspected -- textual
independence is not the same claim. With only `0001`-`0003` applied to a
pristine `025d77f2`, `rust_verify` builds, the toolchain's `vstd` comes out
**2338 verified, 0 errors**, and `traits_dyn`, `traits` and `safe_api` are green
at 50, 230 and 35, 0 failed. `traits_dyn` is 50 rather than the full stack's 57
because the other seven cases are the ones `dyn-spec-fn-generic` appends.

## Rebasing onto `025d77f2`

Done 2026-11-18, 46 upstream commits. Of the 35 files the stack touches, 21 had
moved. The textual rebase took **one** conflict, and the build then found two
more breaks that no merge could have flagged -- which is the shape to expect: a
clean rebase of this stack is not evidence it compiles.

- **`rust_verify_test/tests/traits_dyn.rs`** -- a pure append collision. #3466
  added 182 lines of dyn-compatibility tests at the end of the file, where
  `0001` appends its own; both sides' last test block shares the file's closing
  brace. Resolution is to keep both, upstream's first.
- **`vir/src/modes.rs`** -- #3483 deleted `Ctxt::check_ghost_blocks` (ghost
  blocks are now always checked), which `0004` and `0005` each read in a guard
  (`ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec`). Upstream
  rewrote its own sites by dropping the flag; ours do the same. Fixed in each
  patch separately so every prefix of the stack still builds.
- **`rust_verify/src/trait_conflicts.rs`** -- #3470 (Rust 1.100) removed
  `gen_generics`'s fourth parameter, the `is_impl: Option<&TraitImpl>` hack for
  `Option`'s `Clone` impl. `0001` passed `None` there, so deleting the argument
  is exactly behaviour-preserving.

`0002` survives, and is still worth sending upstream: #3466 *looks* like it
fixes the same bug -- it threads `merged_traits` into
`set_krate_dyn_compatibility` -- but `finish_dyn_compatability_checks`, the
deferred check `0002` repairs, still builds its map from `krate.traits` alone.
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
- `rust_verify/src/trait_conflicts.rs` no longer has `Arc` in scope, so `0001`
  carries `use std::sync::Arc;` itself.

Earlier refreshes: the type-identity patch against `b63c76a4` on 2026-10-21, from `fec4c33a`,
where `Ctx` lost its `pub debug: bool` field upstream (so the patch must no
longer re-add it — it was only ever context) and `vir/src/recursive_types.rs`
grew two `match`es over `TypX` needing a `Primitive::TypeTag` arm, grouped with
the other simple primitives in both.

All five are required unconditionally now that the gates are gone; the last
column says what each one buys rather than which feature used to select it.

| Patch | Supplies | Needed for |
|---|---|---|
| `0001-verus-dyn-supertrait-impls.patch` | supertrait impls for `dyn` types in the trait-conflict checker, transitively and substituted per hop | discharging `dyn T: U`, which `USegment` needs, at any depth |
| `0002-verus-dyn-imported-traits.patch` | lets the deferred dyn-compatibility check see imported crates' traits | any `dyn` of a trait declared in another crate |
| `0003-verus-dyn-reject-diagnostics.patch` | name which `dyn` feature is unsupported, and why | diagnostics only |
| `0004-verus-type-identity.patch` | the `TypeTag` encoding and identity — `type_id::<T>()` for a type, `type_id_of(x)` for a value, related by A1 — plus `vstd/std_specs/any.rs`, and `type_id` of a trait object type as an error rather than a tag nothing relates | `recorded_meta_id` and tagged storage; the erased identity `dyn_meta` and `axiom_untyped_recorded_by_id` report; both sides of the downcast guard; keeping identity honest where the encoding cannot distinguish |
| `0005-verus-any-surface.patch` | `core::any::Any` declared with no methods, so `dyn Any` is a legal type; `is`, `dyn_value` and the downcasts specified | `AnyFrameMeta: Any` and the downcast guard, as upstream writes them |

All five apply with a plain `git apply` to a pristine checkout of that commit,
in order, and together reproduce the tree the counts below were measured
against.

Beside them, applied by nothing: **`verus-dyn-spec-fn-generic.patch`** -- a
`dyn T` value's spec fns related to the erased type generically, and through a
subtrait object. It is intact and still applies, on top of the applied set or at
its old slot ahead of the `Any`-surface patch; it is parked because nothing downstream
needs it. `verus-irc11.patch` is unnumbered for a different reason -- it belongs
to another toolchain entirely.

`0001` covers the supertraits **transitively**, which is not optional for any
hierarchy deeper than one hop. Each emitted `impl U for Dyn<n, ..>` is checked
by rustc against `U`'s own declaration, which carries `where Self: V` for every
supertrait `V` of `U`, so a missing second hop is a *hard error* -- `the trait
bound Dyn<n, ()>: V is not satisfied`, reported against the subtrait's
declaration -- and not the incompleteness the first version of this patch
claimed. `trait R: Q`, `Q: P` plus a `dyn R` anywhere is enough to hit it. The
SMT side needed nothing: `tr_bound%R(DYN%R)` chains through
`trait_bound_axioms` on its own, so only the generated trait-conflict program
lagged. (The transitive half was carried separately as its own patch for a day; it is
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

`0002` is a fix for an upstream bug rather than an extension, and is worth
sending upstream. `well_formed::check_one_typ` admits a `dyn T` whenever `T` is
in the *merged* trait map, which spans imported crates, but it defers the
dyn-compatibility check (the trait's `dyn_compatible` is not yet computed at
that point); `finish_dyn_compatability_checks` then rebuilt its map from
`krate.traits` alone, so a `dyn` of a trait declared in *another* crate was
accepted by the first check and rejected by the second as "not declared to
Verus". Nothing in-tree hit it because a crate's own `dyn` traits are in
`krate.traits`; `ostd` hits it because its `dyn Any` is a `dyn` of a trait
declared *elsewhere* -- `core::any::Any`, declared to Verus by `ExAny` in
`vstd` -- which is still the case after `0005`, with `vstd` now in the role
`vstd_extra` held before it. The symptom when it was measured, against the
`to_any`/`vstd_extra::typing::types::Any` shape that `0005` retired, was five
such errors in the `type_id` shape -- `frame/meta.rs`, `frame/mod.rs`,
`frame/linked_list.rs`, `page_table/node/mod.rs` and
`specs/mm/frame/meta_owners.rs` -- while the declaring crate itself built, since
a `dyn Any` inside it is fine.
The fix feeds the imported crates into that second map, imported first so the
crate being verified still wins a collision. Upstream's own `traits_dyn`,
`traits` and `safe_api` suites (297 tests) pass with it.

`0003` is diagnostics only. `dyn T + Send` and `dyn T<X = u8>` both used to
report "dyn with more than one trait" -- misleading for the first, wrong for the
second, and a message that never described a reachable case, since Rust rejects
two non-auto traits in a `dyn` type itself. Both stay rejected; the error now
names which feature is missing and that `TypX::Dyn` has nowhere to put it.

`0004` carries **both halves of identity**, because they are one model and a
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

`0004` also closes the one place where `type_id` had a tag but no law. (That
was carried separately, as `verus-type-id-reject-dyn`, until 2026-11-23; it is
folded in here, as the same model finished rather than a second change.) Verus
models a trait object type by its trait path and type arguments, which cannot
tell `dyn A` from `dyn B`, so neither the equality nor the disequality of their
tags was provable and a caller got an unexplained `assertion failed` wherever
the identity was finally compared. The alternative was an axiom giving each `dyn` type a
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

`dyn-spec-fn-generic` replaces the per-impl dyn spec-fn axiom's *reach*, not the axiom: the
original fires only once an impl is resolved, so a caller holding `F: T` for a
type parameter learned nothing about an `F` it had erased, and an inherited
supertrait spec fn observed through a subtrait object connected to nothing at
all. Both now follow from one axiom family quantified over the erased type under
the trait's bound. In principle that is what lets a client stop declaring a spec
fn plus a per-impl obligation to recover by hand what the vtable already does.
The per-impl axiom is still emitted; it is the `Self := t0` instance of the new
one, kept until the comparison is measured.

This paragraph used to claim the `meta_id`/`meta_id_correct` deletion as its
payoff. That was `0004`'s -- see above, and see *`verus-dyn-spec-fn-generic`
has no consumer downstream* below, which is the audit that separated them.

`0005` makes `core::any::Any` usable, by declaring it to Verus with **no
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
is upstream's expression. `0005` also carries `dyn_value`, the spec primitive
that lets a downcast name the value it returns -- the coercion is the identity
on the value, so reading it back at the type it was written at returns it -- and
with it `<dyn Any>::downcast_ref` and `Box<dyn Any, A>::downcast`, both
specified and verified end to end. `downcast_mut` is left out: a write through
the extracted reference has to be a write to the erased value, which needs the
converse axiom.

### `verus-dyn-spec-fn-generic` has no consumer downstream

Called `dyn-spec-fn-generic` here, after its file and its `../verus` branch. It
was numbered `0005` while all of this was measured, and is now parked without a
number -- `0005` means the `Any`-surface patch from here on.

Audited 2026-11-23 against **`typeid-rework` at `829ee6e92`**, the branch that
carries the consuming work. Not against this one, which has no consumer at all:
`type_id`, `type_id_of`, `recorded_id`, `dyn_value` and `TypeId` have **zero**
uses in `ostd` and `verified_libs` on `dyn_typing_patches`. Audit the consumer,
not the branch the patches sit on -- getting this wrong makes every patch in the
stack look dead.

Workspace-wide, one trait is used as a `dyn` object *and* declares spec fns --
`AnyFrameMeta` (`on_drop_pre`, `is_untyped_spec`, `usage_spec`, plus
`vtable_ptr`, which is `where Self: Sized` and so off the dyn surface) -- along
with `Payload` in `vstd_extra`'s typing example. Every evaluation of one of
those at a `dyn` receiver:

| site | shape | needs it |
| --- | --- | --- |
| `example.rs` `dispatch(d: &dyn Payload)`, ensuring `r == d.word_spec()` | reflexive **at** `dyn Payload` | no |
| `example.rs` `erase_then_dispatch(v: L2)`, `both_erasures(v: &L2)` | erased type is **concrete** `L2` | no -- the per-impl axiom covers it |
| `meta_owners.rs` `axiom_untyped_recorded_by_id<M: AnyFrameMeta + ?Sized>` | an `axiom fn`: assumed, nothing to discharge | no |
| `meta_owners.rs` `axiom_usage_of_recorded_id`, `lemma_usage_of_held` | `M` is `Sized`, so never `dyn` | no |
| `linked_list.rs` `self.meta.is_untyped_spec()` | receiver is a type param; no erasure | no |
| `segment.rs` `Segment::try_from`, `Segment::is_untyped` | `id_is_untyped(self.meta_id())` | no |

The last row is why this is structural rather than luck. `Segment::is_untyped`
is `id_is_untyped(self.meta_id())` and `meta_id()` reads a ghost field:
untypedness and usage are deliberately properties of the metadata *type*, held
as uninterpreted functions of a `TypeId` and tied to values by `0004`'s
`type_id_of`, which already works at a generic `Self`. `ostd` says so itself --
*"the open-world representation reaches it only through the recorded id."* That
route never needs a spec fn at `dyn` related to one at the erased type, which is
exactly and only what it buys.

So neither of its two capabilities is reached. No erased **type parameter** is
ever compared through a spec fn. And `AnyUFrameMeta: AnyFrameMeta` declares **no
members**, so there is no inherited spec fn to observe through a
`dyn AnyUFrameMeta`; the segment downcast's dyn-to-dyn claim is axiomatized
(`casts.rs`: *"The one claim in the segment downcast that is not proved. Both
sides are `dyn`"*).

Two stale comments turned up in passing, both pointing at a consumer that is not
there: `is_untyped_spec`'s doc says *"the segment downcast observes it through
`&dyn AnyFrameMeta`"*, which the current code does not do, and the
`dyn_frame.dyn_meta().is_untyped()` call in `frame/mod.rs` that would have done
it sits inside a commented-out block.

**And it can be removed, measured the same day.** The audit above is a static
read; this is the disproof it needed, since a trigger can close a goal nobody
designed it for. A toolchain of the five applied patches -- all of which apply in
sequence, no fuzz -- builds, and its own `vstd` comes out **2338 verified, 0
errors**, unchanged. Against it, from a *cleaned* verification target (2427
files, 801.8MiB removed, so each count is a real run rather than a cache hit),
`typeid-rework` at `829ee6e92` gives:

| crate | without it | control, with it |
| --- | --- | --- |
| `ostd` | **1567 verified, 0 errors** | **1567 verified, 0 errors** |
| `vstd_extra` | 764 verified, 0 errors | 764 verified, 0 errors |
| `vstd`, workspace context | 2078 verified, 0 errors | 2078 verified, 0 errors |
| the three small crates | 44 / 23 / 12 / 1 | 44 / 23 / 12 / 1 |

**Run the control arm.** One arm proves nothing here, because the harness is
unusual -- `dv` is a submodule on `typeid-rework`, so it has to be copied in over
the empty directory, and `tools/verus` and `tools/verus-analyzer` are symlinked --
and a harness that returned 1567 regardless of toolchain would have produced
exactly the reported result. The control is the same `typeid-rework` worktree
against the repo's own six-patch `tools/verus`. All seven `verification
results::` lines are identical across the two arms, and the arms really do
differ: `dyn_spec_fn_axioms_generic` greps to 2 in the control toolchain and 0 in
the other, and each worktree's `tools/verus` symlink resolves to a different
tree. A fresh worktree has no verification target, so each is a real run by
construction.

`vstd_extra` is the pointed row: it holds the `Payload` typing example, the only
code in the tree that puts a spec fn through a trait object, and it does not move
-- because the erased type there is a concrete `L2`, which upstream's per-impl
axiom already covers.

One loose thread, recorded rather than claimed: `dv` reported 93.8s for the
verification phase without `dyn-spec-fn-generic` and 109.0s with it. That is the right sign for
an axiom family's quantifier cost, but it is one run each under unequal machine
load, so it is a hint for the per-impl-axiom comparison this file still owes, not
a measurement.

Two traps worth repeating, both of which bit this measurement. **Confirm the
toolchain under test is the one you mean**: here `dyn_spec_fn_axioms_generic`
greps to 0 in it while the upstream per-impl `dyn_spec_fn_axiom` greps to 1, and
`dv`'s own command line names the symlinked checkout. And **do not truncate a
`-p ostd` run**: `ostd` emits six `unused dependency` warnings that will push
every `verification results::` line out of a `tail`, leaving only
`Verified ostd 0.16.0 in 93.24s` -- which, by the rule below, is not a result.

#### `dyn-spec-fn-generic` is not sufficient for `is_untyped` either

`is_untyped` is the fact this patch was for, so the obvious reason to keep it
would be that the fact is coming back. It is not coming back *through this
patch*, and the reason is worth writing down, because the opposite is the natural
assumption.

Where the fact lives now. `Segment::try_from` does not call
`dyn_meta().is_untyped()`; it calls a slot-level helper,

    #[verifier::external_body]
    pub fn is_untyped_at(slot: PPtr<MetaSlot>, Tracked(perm): Tracked<&FrameRawPerms>) -> (r: bool)
        ensures r ==> id_is_untyped(perm.metadata_perm.resource().meta_type_id),
    { unimplemented!() }

and carries the result across the `dyn`-to-`dyn` reparam with
`axiom_segment_untyped_transmutable`, `axiom_segment_reparam` and
`axiom_reparam_perm_narrow_untyped`. So untypedness is a property of a recorded
id in a tracked permission, asserted by a trusted stub. `is_untyped_spec` is
never evaluated at `dyn AnyFrameMeta` in live code.

Why `dyn-spec-fn-generic` cannot serve it, in order of how fundamental:

- **There is no type to instantiate it at.** `is_untyped_at` takes a slot and a
  permission and has **no type parameter**; the metadata's type exists in the
  proof state only as a ghost `TypeId` *value*. Its axiom quantifies over
  the erased *type* under the trait's bound, so using it means supplying `Self`,
  and Verus has no reflection from a `TypeId` back to a type.
- **The receiver is not a coercion.** The axiom triggers on
  `to_dyn%D(Self, .., self!)`. A trait object reconstructed from a vtable word
  read out of the slot is not syntactically the coercion of anything, so the
  pattern cannot match. Closing that needs the converse direction -- the same
  axiom `downcast_mut` is missing -- and `0005`'s `dyn_value<S, T: ?Sized>`
  does not supply it, since it reads a value back at a *named* `S`.
- **The typed value needs the type too.** `typed_meta_value<M: AnyFrameMeta +
  MaxSize<META_STORAGE_SIZE>>` is generic in `M`, and `dyn AnyFrameMeta` does
  not satisfy `MaxSize`.

What *is* sufficient is already in the tree, and needs only `0004`:

    d = dyn_meta(slot)                    ensures type_id_of(d) == self.meta_type_id()
    d.is_untyped()                        ensures res ==> d.is_untyped_spec()
    axiom_untyped_recorded_by_id::<dyn AnyFrameMeta>(d)
                                          d.is_untyped_spec() == id_is_untyped(type_id_of(d))
                                          == id_is_untyped(meta_type_id)                      QED

That is why `is_untyped_spec` is deliberately not `where Self: Sized` and why
`axiom_untyped_recorded_by_id` takes `?Sized`: so the bridge can be instantiated
at the trait object itself. The bridge is stated at the **id** level, which is
exactly what makes the erased type unnecessary. Applied at both `dyn
AnyFrameMeta` and a sized `M`, that axiom plus `0004`'s erasure axiom *derives*
`dyn-spec-fn-generic`'s conclusion for this one spec fn -- so the instance needed here was
axiomatized through the id rather than taken from the general axiom, and the
general axiom would not have reached this call site anyway.

What actually blocks writing `is_untyped_at`'s body is a layer below: `dyn_meta`
and `dyn_meta_ptr` are themselves `external_body` stubs, because, as the comment
there says, *"this fork models slot metadata as a `MetaSlotStorage` rather than
a trait object, so there is no `&dyn` to dispatch on."* Representation, not
axioms.

#### So it is parked, not deleted

What removal costs is the seven `dyn_spec_fn_*` tests and a capability that
works. `dyn-spec-fn-generic` is the most self-contained patch here -- independent of every
other, `0001` included, and buildable and green on a pristine base by itself --
which also makes it the most upstreamable. With `is_untyped` ruled out as a
consumer, that is the whole remaining case for it, and it is a case for sending
it to `verus-lang`, not for carrying it here.

So the patch file stays and **loses its sequence number**: `dv` applies every
`NNNN-*.patch` in this directory and skips the rest, which is how
`verus-irc11.patch` sits beside the stack without joining it. The applied set is
`0001`-`0005`; `verus-dyn-spec-fn-generic.patch` is parked next to
them, unapplied and intact. The `Any`-surface patch took the vacated `0005`, so
the applied set stays contiguous; the numbers are an apply order, not an
identity, which is why every measurement above names patches by what they do as
well as by number.

**The lineage is `asterinas/verus`, not `verus-lang/verus`.** This is the single
most expensive mistake available here. The two forks have diverged, and a
toolchain built from `verus-lang` lacks the `bitvec`/`wyz` specifications `ostd`
now depends on; the symptom is seven *is not supported* / *does not recognize
associated type* errors while compiling **`vstd_extra`**, which looks like a
broken `Cargo.toml` in this workspace and is not. `cargo dv bootstrap` fetches
the right one; prefer it over any hand-managed checkout.

The reference checkout is `../verus`. Three branches there matter:

- **`any-support`** is where development happens: the five applied patches as
  five commits, one per patch and in the same order, based on **`025d77f2`** -- the
  `asterinas/verus` commit `tools/verus` sits on. Rebuilt twice on 2026-11-23
  -- for the merge and then for the reorder, the second at `cb8d1bcce` -- by
  replaying the patch files on the base and reusing the curated messages, so
  **each commit's diff is byte-identical to its patch file**, and the tip tree
  is byte-identical to both `tools/verus` and the tree the patches produce from
  a pristine checkout. Rebuild it that way after any renumbering; nothing else
  keeps the two representations honest. The first rebuild also closed real
  drift:
  the branch still carried the untrimmed comments and the *doubled* diagnostic
  prefix (`assert_vir_error_msg(err, "Verus does not currently support dyn with
  an auto trait")`, where `unsupported_err_span` already prepends that text), so
  its content was three changes behind the patch files. Check the two against
  each other rather than assuming; per-commit `git diff` against the patch file
  is the cheap check and it caught this. `0002` stays cherry-pickable on its own
  for a `verus-lang` PR: it touches `query.rs` and `well_formed.rs`, which
  nothing else in the stack does, and it still applies cleanly to `verus-lang`
  `main`.
  Rebuilt a third time at `07ed52e77` when `dyn-spec-fn-generic` was parked,
  which is also when the `Any`-surface patch's hunk headers were re-emitted --
  they had been computed with the spec-fn patch applied before it, and four of
  them moved once it was not.
- `dyn-spec-fn-generic` at `8042c4767` is the parked patch as a commit, based on
  `any-support`'s type-identity commit so that its diff is byte-identical to
  `verus-dyn-spec-fn-generic.patch`. This is the branch to send upstream.
- `backup/any-support-6-commits` at `cb8d1bcce` is the stack with
  `dyn-spec-fn-generic` still applied at its own number, which is the state the
  control arm above measured.
  The reorder cost one wording fix: the diagnostics patch's message justified
  itself with `type_id::<dyn T>() == type_id::<dyn T + Send>()` becoming
  provable, which now reads as a forward reference, so it says *once type
  identity lands later in this stack*.
- `backup/any-support-identity-first` is the pre-reorder stack at `b9dc03b66`,
  six commits with type identity first.
- `backup/any-support-7-commits` is the pre-merge stack at `aa01ab512`, the
  record of the seven commits before the `type_id`-reject patch was folded
  into type identity.
- `backup/any-support-085772b8` is the pre-rebase stack at `b7a76357c`, kept
  because it is the only record of the stack as it read against the old base.
- `typeid-and-dyn` is the older reference, on the `verus-lang` lineage, carrying
  type identity plus the supertrait work as they stood before this.

Fetch `asterinas/verus` over **HTTPS**, not `origin`: `../verus`'s `origin` is
`git@github.com:asterinas/verus.git`, the SSH key is not always available, and
there is no `origin/main` ref to fall back on --
`git fetch https://github.com/asterinas/verus.git main` is what works. Same for
`verus-lang`, which is the `upstream` remote.

`tools/verus` remains the toolchain this workspace verifies against, and still
holds the changes as uncommitted working-tree edits on top of `025d77f2`.
`../verus`'s own checkout sits on `backup/any-support-085772b8`; no worktree
holds `any-support` any more, so `git -C ../verus switch any-support` just
works.

**Its two internal design docs are gone.**
`source/docs/internal/type-identity-emission.md` and `type-identity-prelude.md`
were the authoritative account of the encoding, were never committed (this file
used to warn about exactly that), and are now absent from `../verus` — whose
tree is clean, with a single stash holding only `trait_conflicts.rs` — and from
`tools/verus`. Nothing in the tree cites them any more — the one file that did,
`verified_libs/vstd_extra/src/typing/types.rs`, was deleted with the feature
gates — so the sections below are the account of record until they are
rewritten, together with `ANY-SUPPORT-PLAN.md`, which is kept with the
downstream work rather than here.

## Refreshing a patch

Regenerate against the **bootstrapped `tools/verus`** or against `any-support`,
which sits on the same commit. Do *not* diff against `../verus`'s **older**
branches, which carry
an earlier generation of this work: that is where the three-way merge and the
hand-resolved `vstd/std_specs/mod.rs` conflict came from, not from the lineage
as such.

### The stack is lineage-neutral

Measured three times -- twice on 2026-11-18, before and after the move to
`025d77f2`, and again on 2026-11-23 after the merge and the reorder -- and
worth re-measuring whenever either fork moves: the patches are **not** specific
to `asterinas`. All five apply in order with a plain `git apply`, no three-way
merge, to `verus-lang/verus` `main` -- at `86e7f117f` from the old base, at
`a95764f23` from the new one, where the `asterinas` base was 3 commits ahead and
7 behind, and at `ffa44851` on 2026-11-23. They also still apply in order to
`ece600feb`, the commit `ci-irc11.yml` pins, both on their own and after
`verus-irc11.patch`.

Measure this with a **sequential** apply and plain `git apply`. Two traps, both
of which produced a false "all six conflict" here: these patch files carry no
`index` lines, so `git apply --3way` cannot find its blobs and degrades to
direct application; and `0005` and the parked patch genuinely fail *standalone*
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
On a `verus-lang` worktree with all of them applied, `cargo build --release --features singular` succeeds, `vstd`
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
    # for k in 1..6: snapshot, git -C $W apply tools/patches/000k-*.patch, snapshot
    # patch k = diff(snapshot k-1, snapshot k), per file

Reordering or merging patches works the same way, with one wrinkle: where two
patches **append** to one file, the later one's context is the earlier one's
added lines, so a reorder conflicts there and nowhere else. Split that file's
final content into its per-patch blocks by hand (the test files have banner
comments marking the boundaries), hand each block to the right step, and let the
replay rebuild the rest. Merging the value-identity patch into the
type-identity patch needed exactly that, in exactly one file.

**Let git do the arithmetic.** For a reorder or a merge, replay the stack as
*commits* in a throwaway clone, move them with `cherry-pick`, and emit each
patch as `git diff <commit>^ <commit> | grep -v '^index '` -- which is exactly
the format of these files, so an unchanged patch comes back byte-identical and
any difference is a real one. Neither of 2026-11-23's two moves needed any
hand-splitting. The `type_id`-reject patch touched only `fn_call_to_vir.rs` and
`tests/type_id.rs`, which no patch between it and type identity goes near. And
the reorder kept the relative order of the two patches that *do* both append to
`traits_dyn.rs`, which is the only place the wrinkle above lives -- type
identity, the patch that moved, does not touch that file at all. Both times the
cherry-picks applied clean and the unmoved patches came back unchanged except
for their hunk headers. Those headers are the reason to re-emit rather
than hand-edit: three of the files had drifted by 8 to 23 lines and `git apply`
had been silently absorbing it, and the `Any`-surface patch carried a malformed
`diff --git a/after/source/...` path from an earlier regeneration. With the
headers right, only `0005` and the parked patch still need predecessors.

**Pass absolute paths.** `git -C <dir> apply <relative>` resolves the patch
relative to `<dir>`, so a repo-relative path silently fails to open.

Then check the result rather than trusting it, and check the *whole tree*, not
just the files you think you touched:

    W=$(mktemp -d)/w
    git -C tools/verus worktree add -q --detach $W 025d77f2
    for p in tools/patches/0*.patch; do git -C $W apply $PWD/$p || echo "FAILED $p"; done
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

    git -C tools/verus apply $PWD/tools/patches/0001-verus-dyn-supertrait-impls.patch
    git -C tools/verus apply $PWD/tools/patches/0002-verus-dyn-imported-traits.patch
    git -C tools/verus apply $PWD/tools/patches/0003-verus-dyn-reject-diagnostics.patch
    git -C tools/verus apply $PWD/tools/patches/0004-verus-type-identity.patch
    git -C tools/verus apply $PWD/tools/patches/0005-verus-any-surface.patch

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

`verus-irc11.patch`, the file beside these, is unrelated to them: it is driven by
`tools/bootstrap-verus-irc11.sh` and `.github/workflows/ci-irc11.yml`, which pin
their own Verus commit (`VERUS_BASE_COMMIT`) and apply that one patch to it.
These five follow the same convention -- a patch file in this directory,
applied to a pinned checkout -- but they are applied *for* you:
`cargo dv bootstrap` and `cargo dv upgrade` apply every `NNNN-*.patch` in this
directory, in numeric order, before building Verus. Add or remove one and
nothing else needs editing; `verus-irc11.patch` is skipped, since it carries no
sequence number. The hook finds how much of the stack a checkout already has by
walking it in **reverse** -- the topmost applied patch is the only one whose
post-image is still intact -- and applies the rest; on a checkout with local
changes that match no patch it stops and says how to reset. The recipe above is
what to run when you want to apply them by hand.

**A checkout can be a superset of the applied set, and `dv` will say nothing.**
After `verus-dyn-spec-fn-generic.patch` was parked, the `tools/verus` that had
been bootstrapped with it still carries it: the reverse walk finds `0005`
intact, returns a full prefix, and reports *already applied*. That is correct
and harmless -- the extra patch is what the control arm measured, and `ostd`
verifies at 1567 either way -- but it means *already applied* means "the applied
set is present", not "the checkout is exactly the applied set". To get the
latter, reverse the parked patch and rebuild, or reset the checkout and
bootstrap again.

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

- `0001` emits supertrait impls for **every** `dyn` trait in the crate, so
  they were never inert with respect to the `dyn_supertrait` gate -- the gate
  controlled which vostd code *relied* on those impls, not whether they were
  emitted. Retiring it changes nothing about the emission.
- `AnyFrameMeta`'s `'static` bound used to be written explicitly, because `Any`
  -- which supplies it upstream -- could not be modelled. The supertrait is back,
  so the bound comes from it again, as upstream has it.

Verify:

    cargo dv verify -p ostd                                 # 1567 verified, 0 errors

Measured 2026-11-18 against `asterinas/verus` `main` at `025d77f2` with the
stack applied, on `typeid-rework` at `b4a530050`, from a cleaned verification
target (see the caching note below -- anything less is a cache hit), and again
after `make fmt`. `vstd_extra` is at **764**, and the `vstd` that ships with the
toolchain builds at **2338** verified, 0 errors.

Upstream's own suites are green on this base too -- eleven of them,
**700 passed, 0 failed**, 5 ignored: `type_id` 29, `any` 10, `traits_dyn` 57,
`traits` 230, `external_traits` 52, `marker_traits` 85, `safe_api` 35,
`traits_modules` 37, `std` 77, `external_fn_specification` 82, `erase` 6. Four
of those counts rose with the move (upstream's own new cases), `traits_dyn`
among them -- #3466's dyn-compatibility tests pass alongside `0005`'s narrowed
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

## Emission inertness of `0004-verus-type-identity.patch`

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
