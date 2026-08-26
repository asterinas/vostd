# Proof Engineering

### Complete external contracts

<!-- guideline: complete-external-contracts -->

An external specification must state every caller obligation and every semantic
fact on which a proof relies: preconditions, postconditions, frame conditions,
well-formedness, and panic behavior.

For example, a `BTreeMap::get_mut` model must preserve entries other than the
selected key and must express the documented compatibility between the stored
key ordering and borrowed-key ordering. A potentially panicking function must
not be specified as `no_unwind`.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3747054386),
[#699](https://github.com/asterinas/vostd/pull/699#discussion_r3763419050), and
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3732701232).

### Centralize trusted boundaries

<!-- guideline: centralize-trusted-boundaries -->

Put an unavoidable specification for an opaque `core`, `alloc`, or `std` API in
the appropriate module under `verified_libs/vstd_extra/src/external/`. Do not
hide a local assumption beside an OSTD caller, and do not treat relocation as a
proof of soundness.

Every unsafe external helper needs contracts strong enough to justify its
callers. Delete an unused helper instead of retaining an unconstrained trusted
boundary.

See also: PR [#674](https://github.com/asterinas/vostd/pull/674#discussion_r3671555470),
[#674](https://github.com/asterinas/vostd/pull/674#discussion_r3687737109), and
[#703](https://github.com/asterinas/vostd/pull/703#issuecomment-5264921275).

### Reuse existing specifications

<!-- guideline: reuse-existing-specifications -->

Before adding a helper, axiom, or external specification, search the active
`vstd` and `vstd_extra` APIs. Use the existing verified operation directly when
it already carries the required semantics.

```rust
// Prefer an existing spec-enabled operation.
let result = lhs.saturating_add(rhs);

// Avoid a duplicate wrapper with an equivalent contract.
```

If existing support is incomplete, extend it at the narrowest reusable layer
instead of creating overlapping local models.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#issuecomment-5225757765),
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3733886308), and
[#699](https://github.com/asterinas/vostd/pull/699#discussion_r3763403672).

### Canonical spec models

<!-- guideline: canonical-spec-models -->

Choose the simplest standard mathematical type that faithfully represents the
executable value. Prefer `Range<int>` for an integer range, `Map` for a map
view, and a sequence plus a position for an ordered cursor when those models
capture the required semantics directly.

Make type-level properties independent of irrelevant value arguments, and make
predicates methods when they describe the well-formedness of one model.

See also: PR [#703](https://github.com/asterinas/vostd/pull/703#discussion_r3763971349),
[#704](https://github.com/asterinas/vostd/pull/704#issuecomment-5265438143),
[#704](https://github.com/asterinas/vostd/pull/704#discussion_r3809917573), and
[#704](https://github.com/asterinas/vostd/pull/704#discussion_r3767737737).

### Explicit well-formedness

<!-- guideline: explicit-well-formedness -->

When a spec-level ghost model cannot use `#[verifier::type_invariant]`, expose a
clear `wf()` predicate and carry it explicitly through operation contracts.
Require well-formedness before an operation and ensure it afterward whenever
the API promises that the state remains valid.

Do not make fields private under the assumption that representation hiding will
cause Verus to establish an invariant automatically.

See also: PR [#704](https://github.com/asterinas/vostd/pull/704#discussion_r3801496837)
and [#704](https://github.com/asterinas/vostd/pull/704#discussion_r3810349440).

### Choose proof resource by scope

<!-- guideline: choose-proof-resource-by-scope -->

Use a tokenized state machine when the verified subsystem is self-contained and
its internal state transitions define the relevant behavior. Prefer composable
permissions or resource algebras when ownership must cross subsystem boundaries
or evolve with loosely coupled kernel components.

Decide from the verification goal and expected composition boundaries, not from
the convenience of encoding the first local transition.

See also: PR [#683](https://github.com/asterinas/vostd/pull/683#issuecomment-5163134765),
[#683](https://github.com/asterinas/vostd/pull/683#issuecomment-5163188523), and
[#683](https://github.com/asterinas/vostd/pull/683#issuecomment-5189197277).
