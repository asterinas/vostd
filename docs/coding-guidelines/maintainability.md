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
state properties. Omit unused named return binders and unit return declarations
such as `-> (ret: ())`.

The expression must match the return type. Keep required casts, such as
`as usize` for a sequence's `nat` length, and justify that the value fits.

See also: PR [#742](https://github.com/asterinas/vostd/pull/742#discussion_r3940933539),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946290469),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946316792),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946322891), and
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3947067359).

### Organize proof imports

<!-- guideline: organize-proof-imports -->

Import proof symbols explicitly instead of repeating long paths in contracts,
lemma calls, `reveal`, and `broadcast use`. Retain qualified paths where an
import would cause ambiguity or obscure a one-off reference.

```rust
use vstd::laws_eq::obeys_eq_spec_properties;

reveal(obeys_eq_spec_properties);
```

Keep new `vstd` and Verus-only imports visibly separate from imports inherited
from executable Rust when the formatter permits it.

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

Import definitions from the same crate within one `use` group, including when
the definitions come from different modules in that crate.

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

See also: PR [#729](https://github.com/asterinas/vostd/pull/729#discussion_r3900385076).

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

Preserve upstream API shapes and round-trip conversion directions. Adapt
ownership with local proof lemmas; do not reverse conversion lemmas, reconstruct
values, add runtime clones, or change caller-facing APIs merely to ease a proof.

See also: PR [#692](https://github.com/asterinas/vostd/pull/692#discussion_r3720382959),
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3720371945),
[#674](https://github.com/asterinas/vostd/pull/674#discussion_r3664166187), and
[#699](https://github.com/asterinas/vostd/pull/699).

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

### Narrow lint suppressions

<!-- guideline: narrow-lint-suppressions -->

Suppress a lint at the smallest item or expression that requires it. Prefer
`#[expect(...)]` when the lint is deliberately triggered so that the compiler
can report when the suppression becomes obsolete.

Avoid crate- or module-wide allowances for a local Verus interoperability issue.

### Right-size spec placement

<!-- guideline: right-size-spec-placement -->

Keep a small, implementation-specific model beside its verified code. Create a
separate file under `ostd/specs/` when the model is substantial, shared, or
expected to grow into a subsystem-level interface.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3740708147)
and [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3740719198).

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
