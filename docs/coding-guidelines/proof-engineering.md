# Proof Engineering

### Complete external contracts

<!-- guideline: complete-external-contracts -->

Before adding or changing an `assume_specification`, check each contract clause
against the source code, API documentation, and relevant comments of the exact
dependency version in use. Resolve discrepancies before trusting the model;
successful verification of callers does not establish the contract's soundness.

An external specification must state every caller obligation and every semantic
fact on which a proof relies: preconditions, postconditions, well-formedness, and panic behavior.

For example, a `BTreeMap::get_mut` model must preserve entries other than the
selected key and must express the documented compatibility between the stored
key ordering and borrowed-key ordering. Exclude documented panic conditions with
explicit preconditions, such as capacity or index bounds, rather than merely
marking the operation `may_panic`. Do not claim `no_unwind` while a panic remains
possible under the preconditions.

Use the library's actual representation limits when modeling size bounds. For
example, the `bitvec` model reviewed in PR #742 bounds bit length and capacity by
`usize::MAX / 8`, not just `usize::MAX`. Keep constructor and mutation
preconditions consistent with the model's length bound.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3747054386),
[#699](https://github.com/asterinas/vostd/pull/699#discussion_r3763419050),
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3732701232),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3940921853), and
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946394200).

### Centralize trusted boundaries

<!-- guideline: centralize-trusted-boundaries -->

Put unavoidable specifications for opaque standard-library or third-party APIs
under `verified_libs/vstd_extra/src/external/`, not beside OSTD callers.
Centralization does not establish soundness: give unsafe helpers contracts that
justify their callers and delete unused helpers.

Prefer `assume_specification`, matching the original generic signature, trait
bounds, and associated types. Before adding an external function wrapper, test
the direct form with the active toolchain and record any concrete obstacle.

See also: PR [#674](https://github.com/asterinas/vostd/pull/674#discussion_r3671555470),
[#674](https://github.com/asterinas/vostd/pull/674#discussion_r3687737109),
[#703](https://github.com/asterinas/vostd/pull/703#issuecomment-5264921275),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3940943084),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3944088308), and
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946352295).

### Restrict generic trusted models

<!-- guideline: restrict-generic-trusted-models -->

Trait bounds and external trait declarations alone do not establish a model's
semantic laws. Inspect associated types, aliasing, and interior mutability; limit trusted
contracts to reviewed type and architecture combinations.

If the external signature must remain generic, guard its guarantees with a
model-validity predicate admitted only for reviewed instances. Include relevant
storage, ordering, and index types.

For example, PR #742 limits its immutable `Seq<bool>` model to `bitvec` storage
`u8`, `u32`, `usize`, and `u64` on 64-bit targets, with `Lsb0`. `BitStore` alone
is insufficient because some implementations allow mutation through shared
references.

See also: PR [#742](https://github.com/asterinas/vostd/pull/742#issuecomment-5549732341)
and [#742](https://github.com/asterinas/vostd/pull/742#issuecomment-5550882161).

### Distinguish spec and exec indexing

<!-- guideline: distinguish-spec-and-exec-indexing -->

`Seq::spec_index` is total, with unspecified out-of-bounds values. Spec helpers
can use this behavior; retain bounds when the claimed property needs a valid
index, and explicit triggers when needed for reliable instantiation.

Executable indexing still requires non-panicking bounds through `requires` or
`IndexSpec::index_req`. A model of executable `get` must preserve its `Option`
success/failure semantics; unspecified spec values do not replace that contract.

See also: PR [#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946386402),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946707985),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3947097938), and
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3947311108).

### Reuse existing specifications

<!-- guideline: reuse-existing-specifications -->

Search the active `vstd` and `vstd_extra` APIs before adding helpers, axioms, or
external specifications. Use existing spec-enabled operations, such as
`saturating_add`, directly. Extend incomplete support at the narrowest reusable
layer rather than introducing overlapping models.

When a checked proof replaces an axiom, call it directly and remove obsolete
wrappers and bridge lemmas. Retain compatibility lemmas only for abstraction
boundaries that current callers need.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#issuecomment-5225757765),
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3733886308),
[#699](https://github.com/asterinas/vostd/pull/699#discussion_r3763403672), and
[#657](https://github.com/asterinas/vostd/pull/657#discussion_r3612471054).

### Canonical spec models

<!-- guideline: canonical-spec-models -->

Choose the simplest standard mathematical type that faithfully represents the
executable value. Prefer `Range<int>` for an integer range, `Map` for a map
view, and a sequence plus a position for an ordered cursor when those models
capture the required semantics directly.

Make type-level properties independent of irrelevant value arguments, and make
predicates methods when they describe the well-formedness of one model.

Prefer standard sequence predicates when they express the property directly:
for example, `bits.all(|b| b)` for a boolean sequence whose elements are all true.
Use a subrange predicate when it improves readability; retain an explicit
quantifier when it better supports the proof's indexing or triggers. A style
simplification does not justify adding an axiom for a fact derivable from the
sequence definition.

See also: PR [#703](https://github.com/asterinas/vostd/pull/703#discussion_r3763971349),
[#704](https://github.com/asterinas/vostd/pull/704#issuecomment-5265438143),
[#704](https://github.com/asterinas/vostd/pull/704#discussion_r3809917573),
[#704](https://github.com/asterinas/vostd/pull/704#discussion_r3767737737),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3947111297), and
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3947117794).

### Implement Inv for models

<!-- guideline: implement-inv-for-models -->

When a spec-level model has an intrinsic validity invariant, implement the
`Inv` trait and define it through `inv()`:

```rust
impl Inv for Model {
    open spec fn inv(self) -> bool {
        // The model invariant.
    }
}
```

Require `inv()` before operations that assume a valid state and ensure it after
operations that promise to preserve validity. For mutable operations, state
this as `old(self).inv()` and `final(self).inv()` where appropriate.

Use a separate `wf(...)` predicate only for well-formedness relationships that
depend on another value. Making fields private provides representation hiding;
it does not cause Verus to establish `inv()` automatically.

See also: PR [#704](https://github.com/asterinas/vostd/pull/704#discussion_r3801496837)
and [#704](https://github.com/asterinas/vostd/pull/704#discussion_r3810349440).
