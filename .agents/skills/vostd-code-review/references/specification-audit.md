# API specification audit

Use this procedure to evaluate API contracts and validate findings with natural
caller scenarios.

## Source analysis

Read scoped APIs, documentation, contracts and callers. Evaluate input admissibility
and meaningful guarantees for every scoped API, including those with populated
postconditions. Inspect macro definitions, attributes and trait contracts where
relevant. Record unresolved facts and generated-item limitations in the report.

Capture function identity, original source span, mode, visibility, verification and
trust status, callable trait/impl contract, return value and mutable outputs. In
`diff` and `pr` modes include functions intersecting changed lines and functions newly
brought into verification by a surrounding macro/attribute/module change. De-duplicate by function
identity, not line count. Supporting callees outside scope cannot become findings.

For each output, inspect `ensures`, `returns`, attribute desugaring and inherited
contracts. Check that callers can establish the next operation's obligations using
the available guarantees, return types and accessible invariants. Identify missing
facts and conditions that constrain only a trivial property, the wrong state or a
vacuous implication. Check effects such as global initialization and ownership
transfer, including functions that return unit.

Evaluate each candidate against the documented behavior and give evidence. Device
reads may genuinely yield arbitrary values; masked reads can still promise bounds
and alignment. Do not equate preserving a wrapper's fields with preserving hardware
state. Prefer abstract frame facts over whole-object equality unless equality is
both justified and appropriate to the abstraction. Check preconditions against the
documented input domain and the caller's available permissions and state.

## Targeted client experiments

The LLM decides whether an experiment could confirm or refute a finding, resolve a
material uncertainty, or validate a suggested correction, then runs it autonomously.
Name the question and how the result would affect the review before running an
experiment. Skip experiments that would add no useful evidence. Record tooling
limitations when they affect a conclusion.

Use scoped contract/client verification in a disposable checkout outside the shared
working tree. This does not permit repository-wide verification, publishing changes,
changing the user's files or adding assumptions/trusted bodies.

1. Materialize the recorded review endpoint in an isolated checkout. For `files`
   mode overlay the captured target bytes and capture any required working-tree
   context; record those hashes. Preserve the original shared checkout and index.
   Use the configured toolchain and separate build artifacts; do not bootstrap or
   upgrade a toolchain as part of a review. If isolation or dependencies are unavailable,
   record the limitation and retain the static result.
2. Write a minimal client from a documented use or real caller, at the same module
   visibility and abstraction boundary. Establish legal, satisfiable preconditions.
   Do not let a client unfold a private body unavailable to its modeled caller or
   strengthen its premises with the fact under investigation. Record adaptations
   and the limits they place on what the experiment establishes.
3. Verify baseline plus client, then the identical client with the minimal candidate
   contract correction and required proof-only support. For excessive `requires`,
   test the relaxed contract against its implementation too. Avoid executable edits;
   if the correction would require one, record a proposed change and limitation
   rather than silently incorporating it into a spec-only experiment.
4. Check that baseline failure is the named obligation, not a parse, visibility,
   unsupported feature or unrelated model failure. Check the corrected implementation
   as well as its client. Strengthening an external contract can make the client pass
   without establishing soundness; document that trust separately. Do not conclude
   repository-wide compatibility from a local pass.
5. Record exact commands, source hashes, toolchain, exit codes, verification counts
   and relevant diagnostics for each variant. Require fresh verifier output: changing
   focus flags or touching a file may only hit cargo-verus caches. A cached `Verified`
   banner is not a new check. Use the supported rebuild mechanism in isolation if
   needed; never clear the shared build cache. If freshness remains uncertain, say so.
   Use a deliberately false contract in a separate disposable variant only when
   necessary to resolve whether a contract was checked. It should fail for the
   expected obligation; it must never become part of the proposed patch.

Stop after the selected premise is resolved or a concrete tooling limitation is
established. Findings need evidence, not repeated solver runs. The orchestrator
checks the recorded evidence without rerunning the persona's experiments.

Return findings and experiment evidence using the shared evidence contract. Include
material unresolved limitations in the evidence check record.
