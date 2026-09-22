# VOSTD Verus Coding Guidelines

These rules for writing and reviewing Verus specifications and proofs draw on
repository policy and VOSTD reviews. They complement `AGENTS.md` and the Verus
documentation.

Use Rust 2021 style and the project formatter configured by `rustfmt.toml`.
Reference guidelines in reviews by their stable kebab-case names.

## Guidelines

### Proof engineering

- [`complete-external-contracts`](proof-engineering.md#complete-external-contracts) — model every relevant precondition, result, frame condition, and panic behavior at an external boundary, mirroring lazy, closure-driven adapter semantics.
- [`centralize-trusted-boundaries`](proof-engineering.md#centralize-trusted-boundaries) — keep unavoidable external specifications in `vstd_extra::external` and make their trust explicit.
- [`restrict-generic-trusted-models`](proof-engineering.md#restrict-generic-trusted-models) — grant trusted model guarantees only to reviewed type and architecture combinations.
- [`distinguish-spec-and-exec-indexing`](proof-engineering.md#distinguish-spec-and-exec-indexing) — use total spec indexing without dropping executable bounds checks or failure semantics.
- [`reuse-existing-specifications`](proof-engineering.md#reuse-existing-specifications) — check `vstd` and existing or upstream models before introducing a new abstraction; remove cheats a verified proof replaces.
- [`canonical-spec-models`](proof-engineering.md#canonical-spec-models) — use the simplest standard mathematical model that preserves the API semantics.
- [`quantifiers-and-triggers`](proof-engineering.md#quantifiers-and-triggers) — use standard predicates and selective triggers to control quantifier instantiation.
- [`implement-inv-for-models`](proof-engineering.md#implement-inv-for-models) — implement `Inv` for intrinsic model invariants a type invariant cannot enforce; never keep `Inv` and `type_invariant` for the same predicate.

### Maintainability

- [`separate-verus-modes`](maintainability.md#separate-verus-modes) — keep executable code, specifications, and proofs visually distinct.
- [`use-chained-comparisons`](maintainability.md#use-chained-comparisons) — express contiguous bounds as one logically equivalent chained comparison.
- [`use-returns-for-exact-results`](maintainability.md#use-returns-for-exact-results) — express exact return values with `returns` and remove unused return binders.
- [`avoid-redundant-as-int-casts`](maintainability.md#avoid-redundant-as-int-casts) — drop `as int` where Verus auto-coerces comparisons and arithmetic, but keep it at spec `int` parameters and standalone `/` divisors.
- [`seq-range-slicing`](maintainability.md#seq-range-slicing) — range-slice a `Seq` or view in specs (`s[i..j]`, `s[i..]`) instead of calling `subrange`/`take`/`skip`; endpoints take any `Integer` type and the inlined desugaring is proof-neutral.
- [`organize-proof-imports`](maintainability.md#organize-proof-imports) — import proof symbols concisely while keeping proof-only dependencies visible and `reveal` calls minimal.
- [`group-imports-by-crate`](maintainability.md#group-imports-by-crate) — stack verification-added imports (`vstd`/`vstd_extra`, then `crate::specs`) above the original import list in blank-line-separated groups the formatter cannot cross, combine same-crate definitions into one `use`, and keep verification-added spec imports separate from inherited exec imports of that crate.
- [`bind-option-payloads`](maintainability.md#bind-option-payloads) — bind a shared `Some` payload once instead of repeating implications and projections.
- [`preserve-exec-code`](maintainability.md#preserve-exec-code) — preserve executable code and source layout while adding proofs.
- [`name-proof-roles`](maintainability.md#name-proof-roles) — name proof functions and resources after their proof and ownership roles.
- [`avoid-unused-spec-helpers`](maintainability.md#avoid-unused-spec-helpers) — add spec and proof helpers only for a current caller or a documented abstraction boundary.
- [`inline-single-use-proof-helpers`](maintainability.md#inline-single-use-proof-helpers) — keep one-off proof steps in their caller instead of adding module-level or associated helpers with a single call site.
- [`defer-auxiliary-proof-functions`](maintainability.md#defer-auxiliary-proof-functions) — keep APIs and critical proofs first; move private auxiliary proof functions to a trailing block at the end of the file.
- [`avoid-redundant-mode-markers`](maintainability.md#avoid-redundant-mode-markers) — do not add `ghost` or `tracked` markers where the enclosing mode already determines the value's role.
- [`prefer-ghost-model-structs`](maintainability.md#prefer-ghost-model-structs) — actively use `ghost struct` for newly added specification- and proof-only types.
- [`keep-internal-spec-helpers-closed`](maintainability.md#keep-internal-spec-helpers-closed) — keep representation-reflecting spec helpers closed and private; reserve `pub open` for the model callers reason about.
- [`document-verified-apis`](maintainability.md#document-verified-apis) — document public verified APIs: a `Verified Properties` block for executable code and one-sentence summaries for spec and proof functions, omitting the block for trivial contracts (field getters, invariant-only mutators).
- [`narrow-lint-suppressions`](maintainability.md#narrow-lint-suppressions) — suppress a lint only at the smallest scope that requires it.
- [`right-size-spec-placement`](maintainability.md#right-size-spec-placement) — keep small local models near their implementation unless they form a reusable subsystem.
- [`document-real-proof-debt`](maintainability.md#document-real-proof-debt) — keep proof comments tied to real source constraints and mark unresolved boundaries explicitly.
- [`qualified-verus-spec-calls`](maintainability.md#qualified-verus-spec-calls) — use qualified paths where `#[verus_spec]` attaches a specification to a call.
- [`pair-exec-helpers-with-spec-models`](maintainability.md#pair-exec-helpers-with-spec-models) — prefer `dual_spec` when one definition serves both modes; otherwise bind an exec helper to a spec twin via `#[verus_spec(returns ...)]` and, when the signature matches, `when_used_as_spec`; keep differently-shaped spec fns where the faithful model needs `int` views or total arithmetic.

### Workflow

- [`inspect-the-owning-model`](workflow.md#inspect-the-owning-model) — follow the target's local model and dependency edges before broadening proof changes.
- [`verify-across-supported-hosts`](workflow.md#verify-across-supported-hosts) — treat host-dependent verification results as a proof robustness problem.
- [`decompose-before-raising-rlimit`](workflow.md#decompose-before-raising-rlimit) — localize and simplify unstable proofs before increasing solver resource limits.
- [`upstream-reusable-specs`](workflow.md#upstream-reusable-specs) — contribute generally useful standard-library specifications upstream after validating them in VOSTD.
- [`preserve-toolchain-configurations`](workflow.md#preserve-toolchain-configurations) — isolate toolchain-specific proofs and verify every supported configuration.

## Supporting patterns

[`proof-patterns.md`](proof-patterns.md) records recurring VOSTD proof shapes that
are useful examples but are not mandatory project-wide rules.
