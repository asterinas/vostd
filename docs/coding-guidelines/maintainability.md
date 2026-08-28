# Maintainability

### Separate Verus modes

<!-- guideline: separate-verus-modes -->

Keep executable code, `spec` functions, proof blocks, and reusable lemmas
visually distinct. A reviewer should be able to see which code runs, which code
defines the mathematical model, and which code exists only to establish a
proof.

Prefer small, coherent groups over interleaving mode changes throughout an
implementation. Keep adjacent verified items in the same `verus!` block when
no ordinary Rust item separates them.

### Preserve exec code

<!-- guideline: preserve-exec-code -->

Add specifications and proofs without rewriting executable Rust or moving its
items. If Verus requires a different executable expression, keep the change
minimal, demonstrate that runtime behavior is unchanged, and make the original
form visible in review.

This includes preserving import-independent item order: proof migration should
not move constants, methods, or module declarations merely to make a partial
file compile.

See also: PR [#692](https://github.com/asterinas/vostd/pull/692#discussion_r3720382959),
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3720371945), and
[#674](https://github.com/asterinas/vostd/pull/674#discussion_r3664166187).

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

See also: PR [#703](https://github.com/asterinas/vostd/pull/703#discussion_r3763958841).

### Document verified APIs

<!-- guideline: document-verified-apis -->

Preserve the original runtime documentation. Add rustdoc for every public
verified API and for proof functions or modules whose properties are important
to callers or proof maintainers.

Describe preconditions, postconditions, and invariants in natural language. The
documentation need not correspond one-to-one with every Verus clause, but it
must cover the critical properties and be understandable to kernel developers
without requiring Verus knowledge.

For a public executable API, add a `Verified Properties` section after its
original documentation. Include:

- `Safety`: State the classes of undefined behavior that have been ruled out
  and identify any remaining trusted boundaries. Do not claim the absence of
  all undefined behavior unless that claim is justified.
- `Functional Correctness`, when applicable: Summarize the behavior established
  by verification.
- `Preconditions`: Explain the obligations that callers must satisfy.
- `Postconditions`: Explain the properties guaranteed on return, including
  whether the function cannot panic when this has been proved.

For a proof function, begin with one sentence summarizing the fact being proved,
followed by `Preconditions` and `Postconditions` sections that explain the
important proof clauses.

For a verified module, add a `Verified Properties` section describing its
verification design, critical invariants, safety properties, and any verified
functional-correctness properties.

Do not merely restate signatures or Verus expressions. Record the information a
caller needs to use the API without reading its implementation or proof.

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

File placement should reduce navigation cost; it should not mechanically split
a short model from its only user.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3740708147)
and [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3740719198).

### Document real proof debt

<!-- guideline: document-real-proof-debt -->

Keep comments that explain a current proof boundary, non-obvious invariant, or
known missing model. Add a `TODO` when a temporary limitation needs follow-up.
Do not copy explanatory comments that are absent from the executable source or
retain comments after the condition they describe is removed.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3820204595)
and [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3819464685).

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
