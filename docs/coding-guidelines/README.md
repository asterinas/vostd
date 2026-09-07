# VOSTD Verus Coding Guidelines

These rules for writing and reviewing Verus specifications and proofs draw on
repository policy and VOSTD reviews. They complement `AGENTS.md` and the Verus
documentation.

Use Rust 2021 style and the project formatter configured by `rustfmt.toml`.
Reference guidelines in reviews by their stable kebab-case names.

## Guidelines

### Proof engineering

- [`complete-external-contracts`](proof-engineering.md#complete-external-contracts) — model every relevant precondition, result, frame condition, and panic behavior at an external boundary.
- [`centralize-trusted-boundaries`](proof-engineering.md#centralize-trusted-boundaries) — keep unavoidable external specifications in `vstd_extra::external` and make their trust explicit.
- [`restrict-generic-trusted-models`](proof-engineering.md#restrict-generic-trusted-models) — grant trusted model guarantees only to reviewed type and architecture combinations.
- [`distinguish-spec-and-exec-indexing`](proof-engineering.md#distinguish-spec-and-exec-indexing) — use total spec indexing without dropping executable bounds checks or failure semantics.
- [`reuse-existing-specifications`](proof-engineering.md#reuse-existing-specifications) — check `vstd` and existing project models before introducing a new abstraction.
- [`canonical-spec-models`](proof-engineering.md#canonical-spec-models) — use the simplest standard mathematical model that preserves the API semantics.
- [`implement-inv-for-models`](proof-engineering.md#implement-inv-for-models) — implement `Inv` for intrinsic model invariants that Verus cannot enforce as type invariants.

### Maintainability

- [`separate-verus-modes`](maintainability.md#separate-verus-modes) — keep executable code, specifications, and proofs visually distinct.
- [`use-chained-comparisons`](maintainability.md#use-chained-comparisons) — express contiguous bounds as one logically equivalent chained comparison.
- [`use-returns-for-exact-results`](maintainability.md#use-returns-for-exact-results) — express exact return values with `returns` and remove unused return binders.
- [`organize-proof-imports`](maintainability.md#organize-proof-imports) — import proof symbols concisely while keeping proof-only dependencies visible.
- [`group-imports-by-crate`](maintainability.md#group-imports-by-crate) — combine definitions imported from the same crate into one `use` group.
- [`bind-option-payloads`](maintainability.md#bind-option-payloads) — bind a shared `Some` payload once instead of repeating implications and projections.
- [`preserve-exec-code`](maintainability.md#preserve-exec-code) — preserve executable code and source layout while adding proofs.
- [`name-proof-roles`](maintainability.md#name-proof-roles) — name proof functions and resources after their proof and ownership roles.
- [`avoid-redundant-mode-markers`](maintainability.md#avoid-redundant-mode-markers) — do not add `ghost` or `tracked` markers where the enclosing mode already determines the value's role.
- [`prefer-ghost-model-structs`](maintainability.md#prefer-ghost-model-structs) — actively use `ghost struct` for newly added specification- and proof-only types.
- [`document-verified-apis`](maintainability.md#document-verified-apis) — document both runtime behavior and proof obligations on public verified APIs.
- [`narrow-lint-suppressions`](maintainability.md#narrow-lint-suppressions) — suppress a lint only at the smallest scope that requires it.
- [`right-size-spec-placement`](maintainability.md#right-size-spec-placement) — keep small local models near their implementation unless they form a reusable subsystem.
- [`document-real-proof-debt`](maintainability.md#document-real-proof-debt) — keep proof comments tied to real source constraints and mark unresolved boundaries explicitly.
- [`qualified-verus-spec-calls`](maintainability.md#qualified-verus-spec-calls) — use qualified paths where `#[verus_spec]` attaches a specification to a call.

### Workflow

- [`inspect-the-owning-model`](workflow.md#inspect-the-owning-model) — follow the target's local model and dependency edges before broadening proof changes.
- [`verify-across-supported-hosts`](workflow.md#verify-across-supported-hosts) — treat host-dependent verification results as a proof robustness problem.
- [`decompose-before-raising-rlimit`](workflow.md#decompose-before-raising-rlimit) — localize and simplify unstable proofs before increasing solver resource limits.
- [`upstream-reusable-specs`](workflow.md#upstream-reusable-specs) — contribute generally useful standard-library specifications upstream after validating them in VOSTD.
- [`preserve-toolchain-configurations`](workflow.md#preserve-toolchain-configurations) — isolate toolchain-specific proofs and verify every supported configuration.

## Supporting patterns

[`proof-patterns.md`](proof-patterns.md) records recurring VOSTD proof shapes that
are useful examples but are not mandatory project-wide rules.
