# Structural sweeps for Verus reviews

Use this procedure within the existing `pr`, `diff`, and `files` pipeline. The
applicable guideline page remains the rule authority. These are search and decision
procedures, not additional review rules or a separate input/output format.

## Inputs, scope and ownership

Use the immutable inputs already captured by the main skill: the committed series
in `pr` / `diff`, or target snapshots and range unions in `files`. Search surrounding
repository context with `rg` as needed; never substitute live target bytes for the
captured input. Keep commit intent associated with its changes. A search may extend
beyond reporting scope, but a finding's primary location must satisfy the main
skill's scope rules. Record unavailable dependency sources as evidence gaps.

Maintainability owns helper consumers, localization and placement in section 1,
section 2, and executable preservation in section 3. Proof engineering owns semantic
reuse in section 1 and tracked-state and quantifier checks in section 3. Each persona
reads its assigned checks and the evidence guidance below; keep API analysis alongside
these checks.

Build a compact candidate list from the relevant declarations, uses, quantifiers
and deletions. Search hits are not findings: inspect enclosing scopes and consumers,
including aliases, macros, traits and cfg conditions. Lexical occurrence counts may
include declarations, recursion or homonyms; similar text does not establish semantic
equivalence. Use targeted searches rather than repeatedly dumping entire files.

## 1. Helper consumers, reuse and placement

Build a small inventory of in-scope `spec fn` and `proof fn` declarations: location,
visibility, semantic role, and consumers. Search symbol references across the
resolved repository and dependency source roots, then inspect the hits. Declarations, comments and self-recursive calls
are not independent consumers. Account for method calls, aliases, macros, trait
implementations, broadcast groups and documented external consumers before deciding.

- **`avoid-unused-spec-helpers`:** With no non-self consumer, check whether the helper
  intentionally defines an abstraction used externally. Public visibility alone is
  not evidence of a consumer. Report an unused helper only when the available source
  and API evidence support the claim; with an incomplete tree, qualify the scope of
  the search and leave external use unresolved. An empty body alone is not dead code.
- **`inline-single-use-proof-helpers`:** For one external caller, examine whether the
  helper adds an independent abstraction used by clients, real reuse, or demonstrated
  solver-context isolation. Merely having an `ensures` clause, or stating a fact that
  could hypothetically be reused, is not evidence of an independent abstraction.
  Check its actual role and consumers. Otherwise keep that proof step in the caller.
  Recursion requires a name,
  not necessarily a module-level API: consider a local named proof function, preserving
  its decreases argument. Do not recommend literal recursive expansion or claim that
  inlining will verify without evidence.
- **`reuse-existing-specifications`:** Inspect both new helpers and repeated inline
  conditions/proof steps. Search by the property being established as well as names:
  receiver/model predicates, existing postconditions, library operations and lemmas.
  Quote both the current expression and the candidate definition. Verify visibility,
  receiver, arguments, modes and logical equivalence, including `Option` presence and
  preconditions. A wrapper with an independent abstraction or stronger result may be
  warranted; an identity forwarding helper needs an actual contract/consumer reason.
  If equivalent predicates live on different receiver shapes, inspect whether both
  can delegate to a shared pure predicate over their relevant views. Do not construct
  a fake tracked receiver merely to reuse its method. A source-supported duplicated
  relation can warrant consolidation even when the exact visibility/refactor needs
  verification; identify the common facts and parameter mapping explicitly.
  Missing vendored sources mean the reuse search is incomplete, not that no reuse exists.
- **`defer-auxiliary-proof-functions`:** Read item order, not just declarations. Identify
  private side-obligation lemmas appearing before the APIs/critical proofs they support.
  Keep public model/spec/proof APIs and `View`/`Inv` implementations with the interface;
  move only internal scaffolding to the trailing helper section. Cite both helper and
  following API locations. Do not classify every private proof as auxiliary.

Also inspect proof-only local bindings introduced or left behind by changed proof
blocks, or within the requested snapshots/ranges in `files` mode. For each candidate, search uses within its lexical scope, accounting for
shadowing and macro capture; a same-named variable in another function is not a use.
An unused ghost snapshot is a local proof-hygiene candidate even when every helper
function has a caller. Cite the enclosing scope and actual use search, not a global
occurrence count.

One helper can be unused, poorly named and misplaced. Preserve distinct actionable
roots, but avoid three redundant remedies when deleting the helper resolves all three.

## 2. Imports, roles and modes

- **`organize-proof-imports`:** Scan qualified paths in contracts, spec bodies, lemma
  calls, assertions, reveals and broadcasts. Inspect the imports and lexical scope
  before proposing a shorter path. Preserve qualification required for ambiguity,
  shadowing or `#[verus_spec]` resolution. Check the page's exception for one-off uses;
  do not assume the rule only concerns `reveal` calls. Check imported free spec/proof
  symbols for actual uses too: an import with no use is a different issue from a long
  qualified call. Exclude wildcard, macro/trait resolution and cfg-dependent cases
  unless their use can actually be ruled out.
- **`group-imports-by-crate`:** Inventory `use` declarations by crate and by permitted
  group (inherited executable imports versus verification additions). Compare within
  each group across modules. Keep cfg-gated imports, visibility/re-exports and aliases
  semantically intact; do not combine groups that the guideline deliberately separates.
  Compare the before-import block too: an inherited runtime import moved into the
  verification group violates preservation of that grouping even if there is only
  one import from its crate. Preserve a leading `::` when needed for disambiguation;
  the path spelling and the placement are separate decisions.
- **`name-proof-roles`:** Classify each proof function by what it establishes or moves:
  reusable fact, trusted axiom, or ownership manipulation. Check the corresponding
  `lemma_`, `axiom_`, or `tracked_` role. Unit return does not preclude ownership effects;
  a tracked argument alone does not establish that role. Preserve trait-required method
  names rather than recommending an incompatible local rename. Check resource type names
  against their actual authority/ownership role, not a preferred spelling.
- **`avoid-redundant-mode-markers`:** Inspect enclosing mode before field/binder syntax.
  Ghost-struct fields inherit ghost; tracked-struct fields inherit tracked, while a
  ghost field in a tracked struct is a meaningful exception. Check proof-only tracked
  tuples separately from executable/mixed boundaries needing `Tracked`/`Ghost` wrappers.
  Never remove a boundary wrapper or a ghost exception merely for visual uniformity.

## 3. Quantifiers and original executable shape

Before treating deleted proof code as removable hints, distinguish assertions from
tracked ownership operations. For a removed `tracked_*` call, inspect the old state
transition, its callee contract, and the next consumer's required state. A permission
removed from a map and not restored may violate a later precondition even if no
runtime instruction changed. Try to locate an equivalent replacement before reporting;
missing verifier execution alone neither proves nor refutes a concrete state-flow gap.

- **`quantifiers-and-triggers`:** Enumerate each universal and existential collection
  predicate, including private lemma contracts and loop invariants; do not stop after
  the first example of a rule. Classify each as element-only or relational. Check
  whether standard `all` / `any` or subrange predicates express the same domain and condition. Inspect their
  actual definitions when available; retain index bounds, cross-index relations,
  empty-sequence behavior and necessary triggers. Index-dependent relationships may
  justify explicit quantification. Do not promise a solver-speed improvement without
  measuring it, or report all explicit quantifiers as defects. Separate the diagnosed
  element-wise pattern from verification of the proposed API spelling: an element
  predicate may capture other arguments or call a method on each element; that alone
  does not make the quantified index essential. Universal and existential element
  tests correspond to all/any respectively. Then write down
  the bounded domain and element predicate, and distinguish it from adjacent-element
  or cross-index relations. If the policy prescribes a collection predicate but its
  dependency definition is unavailable, state the concrete concern and missing
  equivalence/API check in the existing finding fields. The orchestrator assigns
  the verification verdict and any `(unverified)` prefix; the persona does not.
  Do not silently count the rule as satisfied or claim the replacement compiles. If the pattern itself is uncertain,
  record an unresolved check rather than manufacture a violation.
- **`preserve-exec-code`:** Compare before/after executable statements, signatures,
  visibility, and original comments as well as added proof annotations. Read deletions:
  removed provenance comments and runtime documentation are easy to miss in an
  additions-only sweep. For a rewrite, identify the original expression/callee, the
  stated verification obstacle and the required source record. Distinguish a missing
  record from a semantic change (evaluation order, panic behavior, clone, visibility).
  Before recommending a source comment, decide whether the executable rewrite itself
  is necessary. A marker documents a justified minimal change; it does not justify an
  avoidable local binding, changed call, or reordered execution. If necessity is not
  established, prefer preserving the original executable shape with proof annotations
  around it; describe any unverified placement constraint explicitly.
  Without older source/history, do not invent the original code or assert provenance
  was lost before the captured base.

## Evidence and coverage

For each triggered sweep, keep a compact evidence record: inspected items, search
roots or compared locations, resulting finding IDs, and unresolved dependencies.
A search hit is a candidate, not a finding. `not-applicable` requires a checked absence
of the trigger; `complies` requires evidence; a skipped or blocked check is neither.
Use the existing Findings/Compliance fields for this evidence; do not add keys or
return a separate report. Keep records compact. The orchestrator summarizes material
coverage gaps in the final Evidence check record.

When a sweep establishes a concrete, actionable guideline violation, include it as a
finding at an appropriate severity even if it has no runtime consequence. In particular,
unused proof material and import-group violations are ordinarily low-severity findings,
not mere coverage notes. Reserve coverage notes for passed checks, unresolved candidates,
and non-actionable observations. At consolidation, reconcile the candidate list's established
violations with the final findings so a discovered issue is not lost while summarizing.
