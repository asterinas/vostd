# VOSTD Verus Coding Guidelines

These guidelines combine established repository policy and recurring VOSTD
review feedback into a shared standard for writing and reviewing Verus
specifications and proofs. They complement, rather than replace, the operational
rules in `AGENTS.md` and the Verus documentation.

Use Rust 2021 style and run the project formatter. Formatting follows
`rustfmt.toml`, including four-space indentation, crate-level import grouping,
and reordered imports; these mechanically enforced rules are not repeated as
individual guidelines.

Each guideline has a stable kebab-case short name. Use that name in reviews so
that a comment can link to the rule instead of restating it.

## Guidelines

### Proof engineering

- [`complete-external-contracts`](proof-engineering.md#complete-external-contracts) — model every relevant precondition, result, frame condition, and panic behavior at an external boundary.
- [`centralize-trusted-boundaries`](proof-engineering.md#centralize-trusted-boundaries) — keep unavoidable external specifications in `vstd_extra::external` and make their trust explicit.
- [`reuse-existing-specifications`](proof-engineering.md#reuse-existing-specifications) — check `vstd` and existing project models before introducing a new abstraction.
- [`canonical-spec-models`](proof-engineering.md#canonical-spec-models) — use the simplest standard mathematical model that preserves the API semantics.
- [`implement-inv-for-models`](proof-engineering.md#implement-inv-for-models) — implement `Inv` for intrinsic model invariants that Verus cannot enforce as type invariants.

### Maintainability

- [`separate-verus-modes`](maintainability.md#separate-verus-modes) — keep executable code, specifications, and proofs visually distinct.
- [`use-chained-comparisons`](maintainability.md#use-chained-comparisons) — express contiguous bounds as one logically equivalent chained comparison.
- [`prefer-imports-in-proof-code`](maintainability.md#prefer-imports-in-proof-code) — import proof symbols instead of repeatedly writing long fully qualified paths.
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

- [`verify-across-supported-hosts`](workflow.md#verify-across-supported-hosts) — treat host-dependent verification results as a proof robustness problem.
- [`decompose-before-raising-rlimit`](workflow.md#decompose-before-raising-rlimit) — localize and simplify unstable proofs before increasing solver resource limits.
- [`upstream-reusable-specs`](workflow.md#upstream-reusable-specs) — contribute generally useful standard-library specifications upstream after validating them in VOSTD.
- [`preserve-toolchain-configurations`](workflow.md#preserve-toolchain-configurations) — isolate toolchain-specific proofs and verify every supported configuration.
