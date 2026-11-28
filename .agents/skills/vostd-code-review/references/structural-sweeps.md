# Structural sweeps for Verus reviews

Use these search and decision procedures inside the main skill's captured `pr`,
`diff`, or `files` input. The applicable guideline page remains the authority.

## Scope and method

Search repository and dependency context without replacing captured target bytes.
Keep commit intent attached to its changes, enforce the main skill's reporting scope,
and record unavailable sources as evidence gaps. Maintainability owns helper consumers,
placement, imports, roles, modes, and executable preservation; proof engineering owns
semantic reuse, tracked state, and quantifiers.

Build a compact candidate list, then inspect enclosing scopes and consumers. Search
hits are not findings: account for aliases, macros, traits, cfg conditions, declarations,
self-recursion, comments, shadowing, and homonyms. Similar text does not establish
semantic equivalence.

## 1. Helpers, reuse, and placement

Inventory in-scope `spec fn` and `proof fn` declarations with location, visibility,
role, and consumers. Search references across available source roots and inspect hits,
including method calls, aliases, macros, trait implementations, broadcast groups, and
documented external consumers.

- **`avoid-unused-spec-helpers`:** For no non-self consumer, public visibility and an
  empty body are not proof of external use or dead code. Report only when available
  source/API evidence supports the claim; otherwise qualify the search scope.
- **`inline-single-use-proof-helpers`:** For one external caller, test the guideline's
  exceptions against actual use and verification evidence. An `ensures` clause or
  hypothetical reuse is not an independent abstraction. For recursion, preserve a
  named local helper and its decreases argument; do not propose literal expansion or
  promise verification without evidence.
- **`reuse-existing-specifications`:** Check new helpers and repeated inline properties.
  Search existing predicates, postconditions, operations, and lemmas by semantics as
  well as name. Compare the exact expressions, receiver/view shape, arguments, modes,
  visibility, preconditions, `Option` presence, and logical strength. Identify common
  facts and parameter mappings; do not fabricate a tracked receiver. Missing dependency
  sources leave reuse unresolved.
- **`defer-auxiliary-proof-functions`:** Inspect item order. Report only private
  side-obligation lemmas placed before the API or critical proof they support, citing
  both locations.

Also check proof-only locals within their lexical scope, including shadowing and macro
capture. An unused ghost snapshot is a candidate even when every helper has a caller.
Keep distinct actionable roots, but do not multiply remedies when deleting one unused
helper resolves them all.

## 2. Imports, roles, and modes

- **`organize-proof-imports`:** Scan qualified paths in contracts, specs, lemmas,
  assertions, reveals, and broadcasts. Inspect lexical scope before shortening; preserve
  qualification needed for ambiguity, shadowing, `#[verus_spec]`, macros, traits, or
  cfg. Apply the one-off-use exception and separately check imported proof/spec symbols
  for actual use.
- **`group-imports-by-crate`:** Inventory imports by crate and permitted group, comparing
  modules and the before block. Preserve executable-versus-verification grouping,
  cfg, visibility/re-exports, aliases, and a disambiguating leading `::`.
- **`name-proof-roles`:** Classify proof functions as reusable facts, trusted axioms,
  or ownership manipulation, then check `lemma_`, `axiom_`, or `tracked_`. Inspect
  effects rather than return type or one tracked argument; preserve trait-required names.
- **`avoid-redundant-mode-markers`:** Check the enclosing mode. Ghost fields inherit
  ghost and tracked fields inherit tracked, except meaningful cross-mode fields. Treat
  proof-only tuples separately from executable/mixed boundaries requiring wrappers.

## 3. State, quantifiers, and executable shape

For deleted proof code, distinguish assertions from tracked ownership operations. Trace
the old state transition, callee contract, replacement, and next consumer; lack of a
verifier run alone proves neither safety nor a gap.

- **`quantifiers-and-triggers`:** Enumerate universal and existential collection
  predicates, including contracts and loop invariants. Classify element-only versus
  relational predicates and compare their exact domain, condition, empty behavior, and
  triggers with `all`, `any`, or subrange definitions. Universal/existential element
  tests map to `all`/`any`; index-dependent or cross-index relations may justify explicit
  quantification. Do not promise solver improvements or compilation. When definitions
  are unavailable, report the concrete pattern and missing equivalence check as
  unresolved rather than compliance or a manufactured violation.
- **`preserve-exec-code`:** Compare before/after executable statements, signatures,
  visibility, and comments, including deletions. For a rewrite, identify the original
  expression/callee, claimed verification obstacle, source record, and any change to
  evaluation order, panic behavior, clone, or visibility. A marker documents a necessary
  minimal change; it does not justify an avoidable rewrite. Prefer the original shape
  with surrounding proof annotations when necessity is unestablished. Without history,
  do not invent original code or lost provenance.

## Evidence and coverage

For each triggered sweep, record inspected items, search roots or comparisons, finding
IDs, and unresolved dependencies in existing Findings/Compliance fields. `not-applicable`
requires checking that the trigger is absent; `complies` requires evidence; blocked or
skipped checks are neither. The orchestrator owns verification verdicts and summarizes
material gaps.

Concrete actionable guideline violations remain findings even without runtime effect;
unused proof material and import-group violations are ordinarily low severity. Coverage
notes are for passed checks, unresolved candidates, and non-actionable observations.
Reconcile established candidates with final findings during consolidation.
