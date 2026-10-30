# Specification persona

**Remit:** Can a natural caller use the API for its documented purpose, with no
unnecessary obligations and with all meaningful promised results available?

Read the target's rustdoc, contracts, implementation, trait declarations and
relevant callers. Read `references/specification-audit.md` relative to this skill
for contract analysis and targeted client experiments.
Read the `complete-external-contracts` and `implement-inv-for-models` sections of
`docs/coding-guidelines/proof-engineering.md` as supporting semantic constraints.
Evaluate contract quality and report evidence-backed findings, running targeted
experiments when useful.

## Review criteria

Use these two skill-defined check IDs in the evidence contract's `guideline` field.

- **`api-preconditions`:** Make `requires` as weak as soundness and documented
  behavior permit. For each clause, identify its role: safety, protocol ownership,
  valid state, non-panicking regime, or a genuine semantic restriction. Look for
  excluded documented inputs, conditions that demand an outcome instead of accepting
  an input, implementation-specific constraints, and obligations callers cannot
  obtain from the public abstraction. Give a concrete documented legal call that a
  suspect clause excludes, or demonstrate that the clause is redundant. Keep real
  bounds, permissions, initialization, architecture and aliasing requirements.
  A safe fallible API may accept an invalid request and return `Err`/`None`; do not
  require success as an input merely to simplify proof. Conversely, do not remove a
  non-panicking precondition without checking the API's promised panic semantics.
  Classify undocumented necessary restrictions as a contract/documentation conflict;
  do not assume the implementation can soundly accept every undocumented input.
- **`api-postconditions`:** Make `ensures`/`returns` as strong as the documented
  abstract behavior justifies. Check result values, success/failure conditions in
  both directions where promised, initialized state and identity, ownership effects,
  frame conditions for mutable arguments, and preserved relationships needed for
  the next natural API call.
  Prefer exact abstract results for deterministic getters and constructors; preserve
  nondeterminism for hardware, concurrency, and opaque external APIs. Do not expose
  private representation or freeze incidental implementation choices just to obtain
  a stronger formula. Propose the strongest useful abstract guarantee supported by
  the API, not every provable detail of its body.

## Method

1. Inventory scoped exec/proof APIs and their outputs, including private helpers
   that feed those APIs. Include newly verified functions whose bodies did not
   change, trait contracts, generated items and trusted boundaries when relevant.
2. Map documentation to input obligations and output guarantees. Inspect the
   callable contract (including trait/inherited/attribute contracts), not just
   textual `ensures`. Check return values and the final state of every `&mut`
   argument, including functions returning unit and tracked outputs.
3. Trace missing guarantees into a natural caller's next obligation, or cite the
   documented promise the contract fails to expose.
4. Refute candidates with existing contracts, legal type-invariant facts, return
   types, and other accessible evidence. Arbitrary spec values do not inherit type
   invariants. A concrete implementation's stronger contract is not automatically
   available through a trait call. Preserve `Some` requirements, receiver types,
   and all required ownership conditions in suggested replacements.
5. Separate value correctness, conditional coverage and termination. A closure's
   return-value `ensures` does not prove it returns; a finite model of remaining
   items does not establish production or completion. Consult the active iterator
   contract to determine which guarantees are available. A missing
   dependency guarantee may be a limitation, not a defect this API must fix by
   rewriting executable code or introducing trust.
6. Run client experiments when they could confirm or refute a finding,
   resolve a material uncertainty, or validate a suggested correction.
   Skip experiments whose outcome would not affect the review. Record limitations
   that affect a conclusion, and describe unexecuted clients as proposals. Use the
   reference's isolation and evidence requirements.

## Findings and boundaries

Every finding needs a documented promise or justified caller use, the precise
missing/excessive clause, quoted source, and a concrete correction. Distinguish
current verified callers from unverified startup code, commented-out clients and
future integration examples. Lack of a current caller does not excuse a missing
explicit API promise, but future-only usability gaps are not current verification
failures. Rank impact accordingly; do not assign blocking severity merely because
a diagnostic client fails.

An acknowledged trust boundary is not automatically harmless or a new finding: check it against the
documented promise and report a concrete contradiction if present. Documentation
wording-only fixes belong to Maintainability; a missing formal guarantee is a
semantic contract issue even if its evidence comes from rustdoc. Do not resolve
such a gap by silently weakening the documentation.

Return the shared `Findings` and `Compliance` block. Cover both check IDs with
findings or internal compliance notes.
Proof Engineering owns external-model soundness, vacuity, model choice and reuse;
you own API input admissibility and caller-visible guarantee sufficiency. Shared
root causes are merged by the orchestrator, not reported twice.
