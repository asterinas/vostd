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
`lemma_`, axioms with `axiom_`, and helpers that lift ghost-returning operations
into tracked mode with `tracked_`. Name resources after the ownership role they
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

Do not repeat the marker on every field of an already ghost-only struct, and do
not declare a value `tracked` unless it carries linear proof state that requires
tracked handling.

See also: PR [#703](https://github.com/asterinas/vostd/pull/703#discussion_r3763958841).

### Document verified APIs

<!-- guideline: document-verified-apis -->

Add rustdoc to public verified APIs that explains both runtime behavior and the
proof contract. Describe the meaning of important `requires` and `ensures`
clauses, ownership transferred through tracked arguments or results, and any
trusted boundary on which callers rely.

Do not merely restate the function signature. Record the information a caller
needs to use the API without reading its proof.

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
