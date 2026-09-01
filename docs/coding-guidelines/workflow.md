# Verification Workflow

### Inspect the owning model

<!-- guideline: inspect-the-owning-model -->

Start with the target and relevant sibling modules. For code under `ostd/src/`,
inspect the corresponding `ostd/specs/` subsystem when it models the same
concept. Follow imports and fresh verification diagnostics to decide whether a
verified library or architecture/task model belongs in the repair.

Do not inspect or modify every neighboring proof library preemptively. Search
the active `vstd` checkout after checking the owning VOSTD model and local
helpers, especially when the failure concerns an existing standard-library
specification.

### Verify target then repository

<!-- guideline: verify-target-then-repository -->

Use focused verification of the enclosing Rust module while iterating on a
known failure. An item locator such as `path/to/file.rs::item_name` is not a
Verus module path; resolve it to the enclosing module before invoking the
focused command.

Focused verification is partial feedback. Before finalizing proof-sensitive
changes, run the full repository verification gate and report focused-only
success as such when the full gate is unavailable. Use the current commands in
[`AGENTS.md`](../../AGENTS.md#build-test-and-development-commands) rather than
copying command lines into proof documentation.

### Verify across supported hosts

<!-- guideline: verify-across-supported-hosts -->

A proof that succeeds on one supported host but fails on another is not stable.
Run the repository verification gate and the configured Linux/macOS checks for
proof-sensitive changes, especially after a Verus, Z3, or target-architecture
update.

Treat platform-dependent quantifier instantiation or resource-limit behavior as
evidence that the proof needs localization, even when one CI job happens to
pass.

See also: PR [#688](https://github.com/asterinas/vostd/pull/688#issuecomment-5174118963)
and [#674](https://github.com/asterinas/vostd/pull/674#issuecomment-5143566443).

### Decompose before raising rlimit

<!-- guideline: decompose-before-raising-rlimit -->

When a proof times out or becomes solver-version-sensitive, first split a large
proof into smaller lemmas, remove irrelevant context, and make quantifier use
more explicit. Increase `#[verifier::rlimit(...)]` only when the localized proof
still has a justified resource requirement. Keep the limit at or below `200`;
if a proof requires more, decompose or simplify it instead of raising the limit
further.

An `rlimit` increase can be a temporary compatibility measure during a solver
upgrade, but it should remain visible as proof debt and should not replace proof
simplification.

See also: PR [#688](https://github.com/asterinas/vostd/pull/688#issuecomment-5174425113),
[#678](https://github.com/asterinas/vostd/pull/678#issuecomment-5139803494), and
[#681](https://github.com/asterinas/vostd/pull/681#issuecomment-5151453444).

### Upstream reusable specs

<!-- guideline: upstream-reusable-specs -->

When VOSTD develops a generally useful specification for a standard-library
API, validate it against a real VOSTD caller and then propose it to upstream
Verus. Keep the temporary `vstd_extra` model narrowly scoped so that it can be
removed when upstream support lands.

Discuss fundamental missing models, such as the semantics of `Borrow`, with
Verus maintainers before cementing a project-local axiom around them.

See also: PR [#699](https://github.com/asterinas/vostd/pull/699#discussion_r3747182992),
[#704](https://github.com/asterinas/vostd/pull/704#issuecomment-5265453465), and
[#699](https://github.com/asterinas/vostd/pull/699#issuecomment-5354033977).

### Preserve toolchain configurations

<!-- guideline: preserve-toolchain-configurations -->

Proofs that depend on a toolchain branch or experimental memory model must be
isolated behind an explicit configuration. Preserve the default verification
path and verify both the default and experimental configurations in separate CI
jobs.

Keep project-specific toolchain patches in the project fork only when they are
not appropriate as independent upstream changes; record where they came from
and which configuration needs them.

See also: PR [#708](https://github.com/asterinas/vostd/pull/708#issuecomment-5290616590)
and [#708](https://github.com/asterinas/vostd/pull/708#issuecomment-5290899675).

### Finish proof cleanup

<!-- guideline: finish-proof-cleanup -->

Before finalizing a proof-sensitive change, remove redundant assertions, stale
proof-only bindings, obsolete comments, and empty proof blocks when verification
does not need them. Preserve assertions that deliberately expose triggers or
document a non-obvious boundary.

Run the project formatter after cleanup, then repeat focused verification for
the affected modules and the full repository gate. Do not infer success from a
shell pipeline that hides the verification command's exit status.
