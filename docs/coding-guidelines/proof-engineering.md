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
marking the operation `may_panic`. `no_unwind` asserts that the modeled function
never unwinds — an unconditional claim, not one gated by the `requires` clause
(see the [Verus unwinding-signature reference](../../tools/verus/source/docs/guide/src/reference-unwind-sig.md)).
A function with a real panic path, such as `usize::div_ceil` on a zero divisor,
must not carry bare `no_unwind`, even when a `requires` clause excludes the
panicking input: the precondition restricts callers, it does not make the external
function panic-free. Model the no-panic regime faithfully with
`no_unwind when <precondition>` — giving callers the guarantee exactly where
`requires` holds — or omit `no_unwind` when no caller needs it.

```rust
// Never panics: bare `no_unwind` is faithful.
pub assume_specification[ usize::is_power_of_two ](self_: usize) -> (r: bool)
    returns is_pow2(self_ as int)
    opens_invariants none
    no_unwind;

/// `usize::div_ceil` panics if `rhs` is zero; the precondition excludes that case.
pub assume_specification[ usize::div_ceil ](self_: usize, rhs: usize) -> usize
    requires
        rhs > 0,
    returns
        ((self_ + rhs - 1) / (rhs as int)) as usize,
    opens_invariants none
    no_unwind when rhs > 0
;
```

Mirror the standard library's evaluation semantics in adapter contracts. For
closure-driven adapters such as `Iterator::filter` and `map`, the closure runs
lazily when the adapter is consumed, not when it is constructed, so require the
closure's per-element preconditions only where the adapter invokes it, not at
construction time. Do not promise that such an adapter terminates
(`will_return_none` or a decreasing `remaining`) or `no_unwind` unless the
contract requires the closure to terminate and not panic, because the adapter
inherits the closure's behavior and an arbitrary `FnMut` may diverge or panic.

Use the library's actual representation limits when modeling size bounds. For
example, the `bitvec` model reviewed in PR #742 bounds bit length and capacity by
`usize::MAX / 8`, not just `usize::MAX`. Keep constructor and mutation
preconditions consistent with the model's length bound.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3747054386),
[#699](https://github.com/asterinas/vostd/pull/699#discussion_r3763419050),
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3732701232),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3940921853),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946394200),
[#718](https://github.com/asterinas/vostd/pull/718#discussion_r3831831025),
[#718](https://github.com/asterinas/vostd/pull/718#discussion_r3831836346),
[#718](https://github.com/asterinas/vostd/pull/718#issuecomment-5390400295),
and [#770](https://github.com/asterinas/vostd/pull/770#discussion_r4023000538).

### Name assume-spec receivers

<!-- guideline: name-assume-spec-receivers -->

Name the receiver parameters of an `assume_specification` after
their role (`l: &Layout`, `vec: &mut Vec<T, A>`, `b: &bool`), the
naming the [Verus assume_specification guide's examples](../../tools/verus/source/docs/guide/src/reference-assume-specification.md#examples)
use; the guide also rejects `self` in the signature. Rejecting
`self` does not mean spelling the receiver `self_` and dereferencing
it by hand: when the model spec fn takes `self` by value, method-call
auto-deref lets a `&T` receiver call it directly, so write the
deref-free form:

```rust
// Prefer this:
pub assume_specification[ core::alloc::Layout::size ](l: &Layout) -> usize
    returns
        l.spec_size(),

// Over this:
pub assume_specification[ core::alloc::Layout::size ](self_: &Layout) -> usize
    returns
        (*self_).spec_size(),
```

The `&`-receiver form is part of matching the signature — the modeled
method takes `&self`, so the parameter carries `&Layout`, and `&mut T`
where the modeled method takes `&mut self`. What this rule governs is
the binder's name and the deref-free call: a `(*self_)` round trip
adds noise to every read of the boundary file.

See also: PR [#802](https://github.com/asterinas/vostd/pull/802#discussion_r4310053052),
the [earlier deref-naming round](https://github.com/asterinas/vostd/pull/802#discussion_r4114862722),
and the [author's commitment to this rule](https://github.com/asterinas/vostd/pull/802#discussion_r4310705382).

### Centralize trusted boundaries

<!-- guideline: centralize-trusted-boundaries -->

Put unavoidable specifications for opaque standard-library or third-party APIs
under `verified_libs/vstd_extra/src/external/`, not beside OSTD callers.
Centralization does not establish soundness: give unsafe helpers contracts that
justify their callers and delete unused helpers.

Split by where the code lives. A function in this crate that verification
must skip keeps its executable body compiled and type-checked under
`#[verifier::external_body]` paired with a `#[verus_spec]` front door — do
not re-derive it as an assume_specification: PR #770 replaced `num_cpus`'s
assume_specification with an external_body whose `returns` reads the trusted
`cpu_count` model. Reserve `assume_specification` for code outside this
crate — standard-library or third-party signatures — matching the original
generic signature, trait bounds, and associated types. Before adding an
external function wrapper, test the direct form with the active toolchain
and record any concrete obstacle.

Third-party constants that verified code mentions get the same
treatment: consume their values through the boundary file instead of
duplicating them at the call site. A constant gets a per-constant
`assume_specification[ crate::path ] -> T` carrying the trusted
literal, plus a `pub use` re-export of the original constants so
verified code keeps referencing the real symbols (whose names carry
their meaning) rather than a local mirror that can drift from the
source of truth:

```rust
pub use x86::apic::xapic::{XAPIC_EOI, XAPIC_SVR, /* ... */};

verus! {
pub assume_specification[ x86::apic::xapic::XAPIC_EOI ] -> u32
    returns
        0x0B0u32,
;
}
```

See also: PR [#674](https://github.com/asterinas/vostd/pull/674#discussion_r3671555470),
[#674](https://github.com/asterinas/vostd/pull/674#discussion_r3687737109),
[#703](https://github.com/asterinas/vostd/pull/703#issuecomment-5264921275),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3940943084),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3944088308),
[#742](https://github.com/asterinas/vostd/pull/742#discussion_r3946352295),
[#770](https://github.com/asterinas/vostd/pull/770#discussion_r4032586635),
[#770](https://github.com/asterinas/vostd/pull/770#discussion_r4032735266),
[#819](https://github.com/asterinas/vostd/pull/819#discussion_r4226900210),
[#819](https://github.com/asterinas/vostd/pull/819#discussion_r4227263510), and
[#819](https://github.com/asterinas/vostd/pull/819#discussion_r4227300314).

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
layer rather than introducing overlapping models. Before modeling a
standard-library API that `vstd` does not yet cover, also check the Verus
upstream for accepted or in-progress models; if upstream is adding it, reuse or
wait rather than fork a competing local spec, because a second trust source
causes model drift.

When a checked proof replaces an axiom, call it directly and remove obsolete
wrappers and bridge lemmas. Retain compatibility lemmas only for abstraction
boundaries that current callers need. When a verified proof covers a fact
previously admitted with `assume`, `admit`, or `=~=`, remove the cheat instead
of layering proof on top; a change that strengthens verification should
net-reduce the trusted surface, never grow it.

This reaches upstream design as well as local helpers. Before
inventing a model for a hard construct, look for an accepted
upstream Verus form and follow it — PR #819's `external/ptr.rs`
models raw pointer arithmetic per
[verus-lang/verus#3062](https://github.com/verus-lang/verus/pull/3062)
instead of a local invention. Within `vstd_extra`, import an
already-modeled definition before re-declaring anything that looks
like a sibling model — PR #802's `Layout` validity uses vstd's
`valid_layout` rather than restating the documented conditions.
Note reusing the predicate does not by itself discharge validity
for an opaque external type, which still needs its own boundary
axiom (`axiom_layout_model`).

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#issuecomment-5225757765),
[#692](https://github.com/asterinas/vostd/pull/692#discussion_r3733886308),
[#699](https://github.com/asterinas/vostd/pull/699#discussion_r3763403672),
[#657](https://github.com/asterinas/vostd/pull/657#discussion_r3612471054),
[#718](https://github.com/asterinas/vostd/pull/718#issuecomment-5390400295),
[#718](https://github.com/asterinas/vostd/pull/718#discussion_r3826747008),
[#819](https://github.com/asterinas/vostd/pull/819#discussion_r4226871925),
[#819](https://github.com/asterinas/vostd/pull/819#discussion_r4227435187), and
[#802](https://github.com/asterinas/vostd/pull/802#discussion_r4101580272).

### Canonical spec models

<!-- guideline: canonical-spec-models -->

Choose the simplest standard mathematical type that faithfully represents the
executable value. Prefer `Range<int>` for an integer range, `Map` for a map
view, and a sequence plus a position for an ordered cursor when those models
capture the required semantics directly.

Make type-level properties independent of irrelevant value arguments, and make
predicates methods when they describe the well-formedness of one model.
The same test applies to spec helpers: drop a parameter that
every call site passes the same value for, and slice at the
call sites instead — PR #789 reshaped the term
`valid_device_scopes(bytes: Seq<u8>, end: int)` into
`valid_device_scopes(bytes: Seq<u8>)` because `end` was
always `bytes.len()`, and callers now write
`valid_device_scopes(bytes[scope_len..])` with the
[`seq-range-slicing`](maintainability.md#seq-range-slicing) sugar.

See also: PR [#703](https://github.com/asterinas/vostd/pull/703#discussion_r3763971349),
[#704](https://github.com/asterinas/vostd/pull/704#issuecomment-5265438143),
[#704](https://github.com/asterinas/vostd/pull/704#discussion_r3809917573),
[#704](https://github.com/asterinas/vostd/pull/704#discussion_r3767737737), and
[#789](https://github.com/asterinas/vostd/pull/789#discussion_r4060283908).

### Quantifiers and triggers

<!-- guideline: quantifiers-and-triggers -->

Prefer standard predicates such as `Seq::all` when they express the property
directly. Their predicate-based triggers can reduce unnecessary instantiations
compared with broad index triggers such as `s[i]`. Check the predicate's
definition and verify the effect in the actual proof context.

Use a subrange predicate when it improves readability; retain an explicit
quantifier when it better supports indexing or triggers. Do not add an axiom
for a fact derivable from the sequence definition merely to support this change.

See also: [Verus trigger annotations](https://verus-lang.github.io/verus/guide/trigger-annotations.html),
PR [#742](https://github.com/asterinas/vostd/pull/742#discussion_r3947111297), and
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

Prefer a `#[verifier::type_invariant]` when the invariant is one the type
never breaks: every construction is valid and every operation preserves it, so
the checks Verus inserts at constructors, field assignments, and calls taking
`&mut X` succeed without special effort. This covers thin wrappers such as
`CpuId`'s `0 <= self@ < cpu_count()` as well as structural bounds on full
containers such as `MemoryRegionArray`'s `count <= LEN`. Callers then obtain
the fact for free with `use_type_invariant`, instead of threading validity
through every contract. The type must live in the same crate with no fields
public outside it (see the [Verus type-invariant
reference](../../tools/verus/source/docs/guide/src/reference-type-invariants.md)).

One predicate, one mechanism: once a type carries a `type_invariant`, delete
an `impl Inv` that states the same fact and migrate its callers from
`requires inv()` threading to `use_type_invariant`. Keeping both forks the
fact into two proof paths whose definitions drift apart. The removal cascades:
`vstd_extra`'s `InvView` has `Inv` as a supertrait, so the type's `impl InvView`
leaves with it, and callers of `view_preserves_inv` must be updated in the
same pass (PR #782, `MemoryRegionArray`).

Because `type_inv` is `closed`, other modules cannot unfold it; the
cross-module export is a broadcast lemma that requires the invariant
and is triggered on the type's view:

```rust
pub broadcast proof fn lemma_type_inv_range(cpu_id: CpuId)
    requires
        CpuId::type_inv(cpu_id),
    ensures
        #![trigger cpu_id@]
        0 <= cpu_id@ < cpu_count(),
{
}
```

Do not attempt to drop the `requires` on the broadcast lemma so the
caller gets the range for free: broadcast items take spec-mode
parameters, and type invariants only flow through executable
dataflow (`use_type_invariant`), so the empty body cannot
establish its own postcondition. Callers feed the `requires` with
`use_type_invariant(&value)`.

Reach for `Inv` when the invariant breaks transiently or rides on mutating
operations that may panic:

- Type invariants have no supported "temporarily broken" state. A
  construct-then-fix sequence — `CpuSet` fills every word with `!0` and clears
  the nonexistent tail bits only afterwards — is checked mid-sequence, where
  the intermediate value violates the invariant; an `Inv` contract states the
  same operation as `old(self).inv()` and `final(self).inv()` and keeps the
  intermediate state internal. The field-borrow workaround the guide suggests
  restructures executable code, which `preserve-exec-code` rules out.
- A mutator that may panic cannot carry the invariant's exit obligations.
  PR #770 found that `CpuSet::add`'s growth path (`SmallVec::resize`, which
  panics on allocation failure) would force `no_unwind` claims no caller can
  justify; `Inv` leaves panic behavior to each method's own contract.

If a single clause of the invariant makes either case bite, weakening the
invariant and restating that clause as method-level postconditions is a third
lever, trading implicit strength for explicit per-method guarantees.

See also: [`CpuId::type_inv`](../../ostd/src/cpu/mod.rs#L149),
[`lemma_type_inv_range`](../../ostd/src/cpu/mod.rs#L160),
[`impl Inv for CpuSet`](../../ostd/src/cpu/set.rs#L169),
PR [#704](https://github.com/asterinas/vostd/pull/704#discussion_r3801496837),
[#704](https://github.com/asterinas/vostd/pull/704#discussion_r3810349440),
[#770](https://github.com/asterinas/vostd/pull/770#discussion_r4027116647),
[#770](https://github.com/asterinas/vostd/pull/770#discussion_r4034384104),
[#770](https://github.com/asterinas/vostd/pull/770#discussion_r4034932801),
[#782](https://github.com/asterinas/vostd/pull/782#discussion_r4042941132), and
[#812](https://github.com/asterinas/vostd/pull/812#discussion_r4226409753).
