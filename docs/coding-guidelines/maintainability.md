# Maintainability

### Separate Verus modes

<!-- guideline: separate-verus-modes -->

Keep executable code, specifications, and proofs in visually distinct groups.
Keep adjacent verified items in the same `verus!` block when no ordinary Rust
item separates them.

### Use chained comparisons

<!-- guideline: use-chained-comparisons -->

Write contiguous bounds as a single chained comparison when adjacent
comparisons share the same intermediate expressions. Apply this rule in
contracts, invariants, spec predicates, and proof assertions.

```rust
// Prefer this:
fullrange.start <= block.start <= block.end <= fullrange.end

// Over this:
fullrange.start <= block.start
    && block.start <= block.end
    && block.end <= fullrange.end
```

Combine consecutive bound assertions only when logical meaning and proof
behavior are preserved. Do not introduce relations or strengthen contracts to
form a chain.

### Use returns for exact results

<!-- guideline: use-returns-for-exact-results -->

Use `returns expr` for an exact return value and `ensures` for other result or
state properties. This also applies to `assume_specification`. Omit unused named
return binders and unit return declarations such as `-> (ret: ())`.

The expression must match the return type. Keep required casts, such as
`as usize` for a sequence's `nat` length, and justify that the value fits.

See also: PR [#742](https://github.com/asterinas/vostd/pull/742#discussion_r3940933539),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946290469),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946316792),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946322891),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3947067359), and
[#770](https://github.com/asterinas/vostd/pull/770#discussion_r4023879416).

### Avoid redundant `as int` casts

<!-- guideline: avoid-redundant-as-int-casts -->

Drop `as int` where Verus auto-coerces integer types in ghost code, but keep it
where a coercion is genuinely required. Rely on Verus, then keep exactly the
casts the compiler asks for, rather than casting defensively everywhere or
stripping blindly — both create review friction.

Verus compares values of different integer types in ghost code directly, and
the same auto-coercion reaches `*`, `+`, `-` once any operand or literal is
`int`/`nat` (see the [Verus integer guide](../../tools/verus/source/docs/guide/src/integers.md)
on comparisons and `as` coercion). So these casts are redundant:

```rust
// Prefer this:
len == smallvec_view(v).len(),
2 * new_len * size_of::<A::Item>() <= isize::MAX,
r == (self_ + rhs - 1) / (rhs as int),

// Over this:
(len as int) == smallvec_view(v).len(),
2 * (new_len as int) * (size_of::<A::Item>() as int) <= isize::MAX as int,
(r as int) == ((self_ as int) + (rhs as int) - 1) / (rhs as int),
```

Keep `as int` where Verus does not auto-coerce; `E0308` names the operand that
still needs it:

- A `usize`/`nat` argument to a spec function's `int` parameter. The call site
  inserts no coercion, so `Seq::subrange(0, new_len)` and
  `Seq::subrange(0, seq.len())` need `new_len as int` and `seq.len() as int`
  (`Seq::len` returns `nat`; `subrange`'s bounds are `int`). The
  [`seq-range-slicing`](#seq-range-slicing) sugar takes these endpoint types
  directly and avoids the cast.
- A standalone `/` divisor: once the dividend is `int`, `/` expects an `int`
  divisor, so write `(self_ + rhs - 1) / (rhs as int)`, not `/ rhs`.
- A narrowing cast whose target may not hold the value (e.g. `as usize` from a
  sequence's `nat` length), where the cast is the point of the expression.

See also: PR [#770](https://github.com/asterinas/vostd/pull/770#discussion_r4023112584).

### Seq range slicing

<!-- guideline: seq-range-slicing -->

Spec expressions over a `Seq` (or a view, e.g. `bytes@`) support Rust
range-slicing sugar instead of the `subrange`/`take`/`skip` method calls. The
desugaring functions are `#[verifier::inline]` and defined in
`source/vstd/seq.rs`:

| Sugar      | Meaning                               |
| ---------- | ------------------------------------- |
| `s[i..j]`  | `s.subrange(i, j)`                    |
| `s[..j]`   | `s.subrange(0, j)` (via `take`)       |
| `s[i..]`   | `s.subrange(i, s.len())` (via `skip`) |
| `s[i..=j]` | `s.subrange(i, j + 1)`                |
| `s[..=j]`  | `s.subrange(0, j + 1)` (via `take`)   |
| `s[..]`    | `s`                                   |

The endpoints accept any type implementing Verus's `Integer` trait (`int`,
`nat`, `usize`, `u64`, ...), so no `as int` cast is needed, unlike the
method-call forms whose parameters are `int`:

```rust
requires
    valid_utf8(bytes@[size_of::<AnddHeader>()..]),
ensures
    ret.header_spec() == decode_pod::<Header>(bytes@[..size_of::<Header>()]),
```

Prefer the sugar over `.subrange(a, b)`, `.take(n)`, and `.skip(n)` in specs,
contracts, invariants, and assertions. Converting an existing call to the
equivalent sugar is proof-neutral: the desugaring is inlined and definitionally
equal to the call, so the SMT-level expression is unchanged.

The formatter lags the language: `verusfmt` parses the forms with an explicit
start index (`s[i..j]`, `s[i..=j]`, `s[i..]`), but fails on the start-open
forms `s[..j]`, `s[..=j]`, and `s[..]` (verified on 0.7.3, the binary
`cargo dv fmt` runs), and a parse failure skips the whole file. Do not consider
`verusfmt` when choosing among the forms: write the direct equivalent (`s[..n]`
for `take(n)`, `s[n..]` for `skip(n)`, and `s` instead of `s[..]`), and do not
rewrite a spec to appease the formatter.

See also: the range index operators in
[`vstd::seq`](../../tools/verus/source/vstd/seq.rs#L986).

### Organize proof imports

<!-- guideline: organize-proof-imports -->

Import proof symbols explicitly instead of repeating long paths in contracts,
lemma calls, `reveal`, and `broadcast use`. Retain qualified paths where an
import would cause ambiguity or obscure a one-off reference.

```rust
use vstd::laws_eq::obeys_eq_spec_properties;

reveal(obeys_eq_spec_properties);
```

Keep `reveal` and `reveal_with_fuel` minimal. A `reveal` of an `open spec fn`
still adds unfolding fuel and can be load-bearing, so delete a `reveal` only
when verification stays green without it; where a non-obvious `reveal` of an
`open` function must remain, leave a one-line note so reviewers do not strip it.

See also: PR [#718](https://github.com/asterinas/vostd/pull/718#issuecomment-5473172528),
[#718](https://github.com/asterinas/vostd/pull/718#issuecomment-5473348502),
[#718](https://github.com/asterinas/vostd/pull/718#discussion_r3840368904),
and [#718](https://github.com/asterinas/vostd/pull/718#discussion_r3955173853).

### Group imports by crate

<!-- guideline: group-imports-by-crate -->

Lay out the import section as verification-added groups above the imports
inherited from the executable Rust, separated by blank lines:

```rust
use vstd::{...};
use vstd_extra::{...};

use crate::specs::{...};

// Imports inherited from the original source, unchanged:
use ...;
```

The first group collects the new `vstd` and `vstd_extra` imports (together
with spec uses of other crates, per the exception below); the second holds
this file's `crate::specs` model imports (see
[`right-size-spec-placement`](#right-size-spec-placement)); and the last
block is the original import list, left unchanged. The blank lines are
load-bearing: on the pinned stable toolchain the formatter ignores the
unstable `imports_granularity`/`group_imports` options in `rustfmt.toml` and
reorders `use`s only within a contiguous run, never across a blank line. Drop
the blank lines and the whole run is alphabetized, sinking `crate::specs`
among the original imports and pushing `vstd`/`vstd_extra` to the bottom.

Within each group, import definitions from the same crate in one `use`
statement, including when the definitions come from different modules in
that crate.

```rust
// Prefer this:
use vstd::{
    laws_cmp::{obeys_cmp_ord, obeys_cmp_partial_ord, obeys_partial_cmp_spec_properties},
    laws_eq::obeys_eq_spec_properties,
};

// Over this:
use vstd::laws_cmp::{
    obeys_cmp_ord, obeys_cmp_partial_ord, obeys_partial_cmp_spec_properties,
};
use vstd::laws_eq::obeys_eq_spec_properties;
```

Exception for verification-added spec imports: a newly added `use` that
introduces spec or proof symbols (spec functions, models, lemmas) stays in
the Verus-actor import group and is not merged with a pre-existing `use` of
the same crate that imports executable items; the blank-line separation
between the verification-added groups and the original import list takes
precedence over this rule's merging for such pairs.

```rust
// Added with the proof, spec models of a crate that also has an exec import:
use ostd_pod::{decode_pod, from_bytes_spec};

// Pre-existing executable import, inherited with the executable Rust — not merged:
use ostd_pod::Pod;
```

See also: PR [#729](https://github.com/asterinas/vostd/pull/729#discussion_r3900385076)
and [#792](https://github.com/asterinas/vostd/pull/792#issuecomment-5748471711).

### Bind Option payloads

<!-- guideline: bind-option-payloads -->

When two or more facts depend on the payload of the same `Option`, bind the
payload once with `matches` and group the facts in an implication block.

```rust
// Prefer this:
result matches Some(value) ==> {
    &&& value.start <= value.end
    &&& valid(value)
},

// Over this:
result is Some ==> result->0.start <= result->0.end,
result is Some ==> valid(result->0),
```

Use a descriptive binder and preserve the original conditions. Leave a single
implication ungrouped unless the binding improves clarity.

See also: PR [#728](https://github.com/asterinas/vostd/pull/728#discussion_r3893413063).

### Preserve exec code

<!-- guideline: preserve-exec-code -->

Add specifications and proofs without rewriting executable Rust or reordering
constants, methods, or modules. If Verus requires an executable change, keep it
minimal, demonstrate unchanged runtime behavior, and show the original form in
review.

When verification does add, remove, or rewrite executable Rust relative to the
original source, mark the modification with one block comment immediately
before the modified code — at the original location for a pure removal with no
replacement. The comment contains, in this order: a brief, concrete reason the
executable code must differ, naming the Verus or vstd limitation when there is
one instead of a vague "needed for verification"; and the original code,
introduced by the exact label `Origin Rust:`, preserved accurately enough to
compare control flow, calls, arguments, operators, and side effects:

```rust
/* `Iterator::sum` has no model in the active vstd, so use an indexed loop with a
 * prefix-sum invariant while preserving the same word order and arithmetic.
 * Origin Rust: self.bits
 *     .iter()
 *     .map(|part| part.count_ones() as usize)
 *     .sum()
 */
```

Continue a multi-line original on the following `*` lines; a one-line original
stays on the label line. One comment covers one contiguous modified block, and
neither a distant comment nor Git history substitutes for it. For executable
code with no corresponding original statement, write `Origin Rust: <none; new
executable code>`. Changes confined to `spec`, `proof`, ghost/tracked state,
Verus attributes, or comments carry no marker. (The literalized constant below
keeps its original on adjacent line comments — the single-line form of the same
practice.)

In review, treat a modification as noncompliant when its comment is missing,
not immediately adjacent, not a block comment, omits the reason or the `Origin
Rust:` label, puts the original before the reason, or does not faithfully
represent the original. A compliant comment records why the executable code
must differ; whether runtime behavior is preserved is reviewed separately.

Preserve upstream API shapes and round-trip conversion directions. Adapt
ownership with local proof lemmas; do not reverse conversion lemmas, reconstruct
values, add runtime clones, or change caller-facing APIs merely to ease a proof.

When a constant the specs must mention derives from constructs specs cannot
see, literalize it and keep the original definition as a comment beside the
replacement, including the equivalence the literal enables: `const
BITS_PER_PART: usize = 64;` carries `// Original exec: ... size_of::<InnerPart>() * 8;`
with the `exec % BITS_PER_PART ↔ spec % 64` note, so the value stays reviewable.

See also: PR [#692](https://github.com/asterinas/vostd/pull/692#discussion_r3720382959),
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3720371945),
[#674](https://github.com/asterinas/vostd/pull/674#discussion_r3664166187),
[#770](https://github.com/asterinas/vostd/pull/770#discussion_r4042957946),
[#699](https://github.com/asterinas/vostd/pull/699), and the live `Origin Rust:`
markers in [`CpuSet::count`](../../ostd/src/cpu/set.rs#L229),
[`is_empty`](../../ostd/src/cpu/set.rs#L272),
[`is_full`](../../ostd/src/cpu/set.rs#L313), and
[`iter`](../../ostd/src/cpu/set.rs#L408).

### Name proof roles

<!-- guideline: name-proof-roles -->

Use `snake_case` for modules and files, `CamelCase` for types and traits, and
`SCREAMING_SNAKE_CASE` for constants. Prefix proved reusable facts with
`lemma_`, axioms with `axiom_`, and helpers that manipulate tracked variables
with `tracked_`. Name resources after the ownership role they
represent, especially when several resources belong to the same protocol.

```rust
proof fn lemma_mapping_preserved(...) { ... }
proof fn tracked_borrow(...) -> (...) { ... }
```

Avoid broad names such as `CpuCore` or indistinguishable protocol resource names
when the type actually represents a specific authority, owner, pool, or state.

See also: PR [#679](https://github.com/asterinas/vostd/pull/679#discussion_r3690850716),
[#723](https://github.com/asterinas/vostd/pull/723#discussion_r3849117460),
[#723](https://github.com/asterinas/vostd/pull/723#issuecomment-5392419977), and
[#672](https://github.com/asterinas/vostd/pull/672#issuecomment-5099747820).

### Avoid unused spec helpers

<!-- guideline: avoid-unused-spec-helpers -->

Add a `spec fn`, `proof fn`, or proof-only model operation only when it has a
current caller or defines an intentional abstraction boundary with a documented
external consumer. Search for call sites before adding the helper and again
before review. Do not expand the specification API merely for symmetry,
convenience, or anticipated future proofs; add the operation with the proof
that needs it. Remove newly introduced helpers that remain unused.

See also: PR [#778](https://github.com/asterinas/vostd/pull/778#discussion_r4045503423).

### Inline single-use proof helpers

<!-- guideline: inline-single-use-proof-helpers -->

Keep a proof step in its caller when it has only one call site and does not
define an independent abstraction. Before adding a module-level or associated
`proof fn`, search its call sites. If there is only one, put the proof body at
that call site. When recursion or another language constraint requires a named
function, define a local `proof fn` inside the caller so the helper does not
expand the surrounding module's proof API.

Retain a separate proof function only when it provides real reuse, states a
fact that callers should depend on as an abstraction boundary, or demonstrably
isolates proof context needed for reliable verification. Do not extract a
helper merely to name a short proof block or structure generated proof code.
Likewise, delete a trivial helper when its fact verifies directly at the call
site.

See also: PR [#775](https://github.com/asterinas/vostd/pull/775#discussion_r4032713402),
[#718](https://github.com/asterinas/vostd/pull/718#discussion_r3920738708), and
[#718](https://github.com/asterinas/vostd/pull/718#discussion_r3920718897).

### Defer auxiliary proof functions

<!-- guideline: defer-auxiliary-proof-functions -->

Order a verification-heavy module so that a top-down read presents the APIs and
critical proofs first: types, public `spec fn`s, `View` and `Inv`
implementations, and the verified executable functions stay in the upper part
of the file. Move private auxiliary `proof fn`s to a trailing `verus!` block
at the end of the file, opened by a one-line comment naming the section.
Auxiliary here means lemmas that discharge side obligations — such as
bounds-fitting or representation-to-model bridge facts — which serve the
proofs rather than state the module's contracts.

Item order carries no semantics: a proof function can be called before its
textual declaration, so deferring helpers is a layout-only change with no
effect on name resolution or verification results. Keep public spec and proof
functions in the API part, though — callers name them in their own contracts,
so they belong to the module surface, not to internal scaffolding.

See also: the deferred lemma block in [`cpu::set`](../../ostd/src/cpu/set.rs#L794),
called from [`CpuSet::new_full`](../../ostd/src/cpu/set.rs#L193), and
PR [#770](https://github.com/asterinas/vostd/pull/770#discussion_r4042969977).

### Avoid redundant mode markers

<!-- guideline: avoid-redundant-mode-markers -->

Use `ghost` and `tracked` markers where they communicate or enforce a mode
boundary. Prefix proof-only fields inside executable types with `ghost_` or
`tracked_` so their erasure and ownership role are visible:

```rust
pub struct Foo {
    value: u64,
    tracked_permission: Tracked<Permission>,
    ghost_model: Ghost<Model>,
}
```

Do not repeat the marker on every field of a `ghost struct`.
For a `tracked struct`, fields are `tracked` by default,
so we need to add `ghost` marker to fields that are not linear ownerships.

Within proof functions, pass and return tracked resources with tracked binders.
Do not wrap every component of an all-tracked proof tuple in `Tracked<_>`;
reserve `Tracked<T>` and `Ghost<T>` wrappers for executable or mixed-mode
boundaries where erased values must cross an executable signature.

See also: PR [#656](https://github.com/asterinas/vostd/pull/656#issuecomment-5019089808)
and [#703](https://github.com/asterinas/vostd/pull/703#discussion_r3763958841).

### Prefer ghost model structs

<!-- guideline: prefer-ghost-model-structs -->

Choose each new struct's mode explicitly and confirm it with verification:

- Try `ghost struct` first for proof-only models, constants, and invariant markers,
  including zero-sized types used as generic arguments.
- Use `tracked struct` for linear permissions, tokens, or ownership. An all-ghost
  tracked type should be ghost unless an ownership protocol needs its identity.
- Keep an ordinary struct for runtime state or other executable behavior.

See also: PR [#728](https://github.com/asterinas/vostd/pull/728#discussion_r3893393342).

### Keep internal spec helpers closed

<!-- guideline: keep-internal-spec-helpers-closed -->

Distinguish the API's reasoning surface from helpers that reflect the concrete
representation. A spec fn consulted only by its own module's proofs — one
describing a bitset's backing words, say — should remain a `closed spec fn`
with private visibility; widening it to `pub open` binds callers to the
representation and invites unfolding outside the module.

Reserve `pub open spec fn` for the model callers reason about in contracts.
When an outer module genuinely needs a representation fact, export a lemma
that carries the fact instead of exposing the helper.

See also: PR [#770](https://github.com/asterinas/vostd/pull/770#discussion_r4044364876)
and [#770](https://github.com/asterinas/vostd/pull/770#discussion_r4044824466).

### Document verified APIs

<!-- guideline: document-verified-apis -->

Preserve runtime documentation. Add rustdoc for public verified APIs and proof
functions or modules whose properties matter to callers or maintainers. Explain
critical contracts and invariants in language kernel developers can understand,
without restating every Verus clause.

For public executable APIs, append a `Verified Properties` section containing:

- `Safety`: Identify the classes of undefined behavior ruled out and remaining
  trusted boundaries. Claim only what verification establishes.
- `Functional Correctness`, when applicable: Summarize the verified behavior.
- `Preconditions`: State caller obligations.
- `Postconditions`: State return guarantees, including absence of panic if proved.

Format the section as level-2 rustdoc subsections, not inline fields: write
`## Safety`, `## Functional Correctness`, `## Preconditions`, and
`## Postconditions` in that order, and give each verified fact its own `-`
bullet so the bullets mirror the conjuncts of the function's
`requires`/`ensures`. Do not merge the fields into single inline entries such
as `- Safety: ...`. Keep a verified module's `Verified Properties` paragraph
as prose.

Omit the section when the verified contract adds nothing beyond the signature
and the type's own invariant. Two common cases:

- **Field getters** — the spec only fixes the return value to a field or a spec
  function of it (`returns` / `ret == self.field`); the one-line rustdoc
  summary ("Gets the end physical address of the contiguous frames.") already
  says everything the section would.
- **Invariant-only mutators** — the only `requires`/`ensures` clauses are
  `inv()` being required and re-established, with no verified functional
  relationship between `old(self)` and `final(self)`.

In both cases keep the ordinary rustdoc summary — the exemption is from the
`Verified Properties` block, not from documenting the item. Write the block
once any clause goes further: a functional postcondition relating `old(self)`
and `final(self)`, a `Safety` claim, or a guarantee not evident from the
accessor's body.

The `Preconditions` and `Postconditions` fields apply to executable APIs only.
Spec and proof functions are erased at runtime; their `requires` and `ensures`
clauses already state obligations and results formally, so do not add
`Preconditions` or `Postconditions` sections that merely restate them (see
[`document-real-proof-debt`](#document-real-proof-debt)). Document a `spec fn`
with the mathematical meaning of the value it denotes, and a `proof fn` with one
sentence summarizing the proved fact; add further prose only when an obligation
or guarantee is non-obvious and not apparent from the signature.

For verified modules, add a `Verified Properties` section covering verification
design, critical invariants, safety, and any verified functional correctness.

See also:
[`SpinLock`](../../ostd/src/sync/spin.rs#L18),
[`AlignExt`](../../ostd/libs/align_ext/src/lib.rs#L98), and
[`entails_and_temp_reverse`](../../verified_libs/vstd_extra/src/temporal_logic/rules.rs#L793).
A canonical subsection-formatted block:
[`VmSpace::reader`](../../ostd/src/mm/vm_space.rs#L347).
An omitted block for a field getter:
[`Segment::start_paddr`](../../ostd/src/mm/frame/segment.rs#L507).

### Narrow lint suppressions

<!-- guideline: narrow-lint-suppressions -->

Suppress a lint at the smallest item or expression that requires it. Prefer
`#[expect(...)]` when the lint is deliberately triggered so that the compiler
can report when the suppression becomes obsolete.

Avoid crate- or module-wide allowances for a local Verus interoperability issue.

### Right-size spec placement

<!-- guideline: right-size-spec-placement -->

Keep a small, implementation-specific model beside its verified code. Create a
separate file under `ostd/specs/` when the model is substantial (e.g., more
than about 200 lines), shared, or expected to grow into a subsystem-level
interface.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3740713899).

### Document real proof debt

<!-- guideline: document-real-proof-debt -->

Keep proof comments brief and focused on non-obvious, current constraints and
their consequences. Document shared trust boundaries once at module level.
Avoid restating code, speculating about tool limitations, or recounting failed
proof attempts. Update or remove comments when the constraints change.
Add a `TODO` for temporary limitations that need follow-up.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3820204595),
[#699](https://github.com/asterinas/vostd/pull/699#discussion_r3819464685),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3940894244),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3940913907), and
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3943825219).

### Qualified Verus spec calls

<!-- guideline: qualified-verus-spec-calls -->

When attaching `#[verus_spec]` to a function call, use a qualified path if name
resolution through an import prevents Verus from finding the specification.

```rust
let slot = (#[verus_spec(with Tracked(slot_perm))]
    crate::mm::frame::meta::get_slot(frame));
```

Prefer this local, explicit workaround over adding an import solely to change
how the attribute resolves the callee.

See also: PR [#673](https://github.com/asterinas/vostd/pull/673#discussion_r3662337926)
and [#673](https://github.com/asterinas/vostd/pull/673#discussion_r3662532282).

### Pair exec helpers with their spec models

<!-- guideline: pair-exec-helpers-with-spec-models -->

Keep an executable helper and its model attached instead of duplicating the
formula independently in each mode. Prefer the lightest mechanism that keeps
both modes honest:

- `#[verus_verify(dual_spec)]` when the body is already a spec-compatible
  expression — one definition serves both modes (`paddr_to_vaddr`,
  `MemoryRegion::new`). Write its `#[verus_spec]` self-referentially
  (`returns f(args)`), or exec call sites get no model facts; `dual_spec,
  open` requires the function to be `pub` (bare `dual_spec` stays
  module-visible like `closed`).
- Otherwise pair the exec function with a spec twin that carries the faithful
  definition, bound by `#[verus_spec(returns twin(...))]`: `part_idx`'s body
  calls `CpuId::as_usize()`, which spec mode cannot, so `part_idx_spec(i: int)`
  holds the formula.
- Add `#[verifier::when_used_as_spec(twin)]` when the twin's signature
  matches, and spec mode can call the helper by its exec name
  (`parts_for_cpus`, `sub_ptr::to_repr`).

Keep a spec fn with different argument types when the truthful model requires
a shape the exec helper cannot offer:

- plain integer views, such as `bit_idx_spec` taking an `int` so proofs can
  also address padding bits outside the valid CPU range;
- total arithmetic replacing panicking executable operations, such as a
  ceiling-division `parts_for_cpus_spec` instead of calling `usize::div_ceil`,
  whose contract carries preconditions and panic behavior.

Forcing such a helper into spec mode through `when_used_as_spec` would import
the panicking operation's obligations into every spec call, or require
re-signing the executable function, which
[`preserve-exec-code`](#preserve-exec-code) rules out.

See also: PR [#770](https://github.com/asterinas/vostd/pull/770#discussion_r4032758336),
[#770](https://github.com/asterinas/vostd/pull/770#discussion_r4035293382),
and [#770](https://github.com/asterinas/vostd/pull/770#discussion_r4035681677).
