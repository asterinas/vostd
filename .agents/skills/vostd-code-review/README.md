# VOSTD Code Review

`vostd-code-review` reviews either a Git change or selected Verus source
files against the VOSTD coding guidelines and writes a single, evidence-backed
Markdown report. It covers maintainability, proof engineering and API specification
quality (weak sufficient preconditions and strong faithful postconditions), plus
two conditional workflow checks, in
[`docs/coding-guidelines`](../../../docs/coding-guidelines/README.md).

## Usage

The skill has three modes:

```text
$vostd-code-review diff [<base>] <output> [--overwrite]
$vostd-code-review files <target[:lines] ...> <output> [--overwrite]
$vostd-code-review pr <pr-link> <output> [--overwrite]
```

Examples:

```text
$vostd-code-review diff review.md
$vostd-code-review diff main review.md
$vostd-code-review diff origin/main review.md --overwrite
$vostd-code-review files ostd/src/sync/rwlock.rs review.md
$vostd-code-review files ostd/src/sync/rwlock.rs:120-240 review.md
$vostd-code-review pr https://github.com/asterinas/vostd/pull/860 review-860.md
```

`diff [<base>]` reviews the committed series
`merge-base(<base>, HEAD)..HEAD`, oldest first. When `<base>` is omitted it defaults to
`origin/main`, the `main` branch of the upstream `origin`
(https://github.com/asterinas/vostd); run `git fetch origin` first to review against the
latest upstream main. Each commit's message and diff are captured together so reviewers
can judge the code against that commit's intent. Uncommitted changes are excluded. To
review a historical endpoint, check it out first so it becomes `HEAD`.

`files` reviews the current working-tree contents of the named files, including
staged, unstaged, and untracked target content. Targets use 1-based inclusive
line ranges. Repeat a path to review multiple ranges from the same file. If no
range is supplied, the whole file is in scope.

`pr` fetches the linked PR's head and the latest upstream `main`, switches the current
repository to the PR head in detached HEAD state, then reviews the committed series
`merge-base(main, head)..head`. The comparison always uses `main`. Fork PRs are
supported through the upstream PR head ref. The report records the URL and exact
head/main SHAs, and the checkout stays at the reviewed PR head. Local modifications
are preserved; a conflicting or dirty tracked checkout is reported before proceeding.

In all modes, the output path is the final positional argument and is not
overwritten unless `--overwrite` is present.

## What the review does

The skill:

1. snapshots the commit series or current working-tree target contents;
2. runs isolated reviews for maintainability and proof engineering, plus a
   Specification pass when APIs/contracts or newly verified APIs are in scope;
3. runs a workflow review only when an `rlimit` changes or a `std`/`core`/`alloc`
   external specification is newly added or materially changed;
4. checks important claims against the source, the complete active `vstd`, and existing
   verified code throughout VOSTD;
5. consolidates the results by severity; and
6. writes an English Markdown report containing findings and evidence-check details.

The workflow pass checks only whether a changed rlimit exceeds `200` and whether a
newly added or materially changed project-local external specification for a
`std`/`core`/`alloc` API should be proposed upstream. It does not review CI or host
coverage, toolchain configuration, solver stability, proof decomposition, or other
workflow concerns.

The Specification pass compares documented admissible inputs and promised results
with caller-visible contracts. The LLM inventories APIs, judges contract sufficiency
and checks natural caller scenarios. Device reads can intentionally be unconstrained,
while a mentioned result can still have an inadequate contract.
The procedure is maintained in [`references/specification-audit.md`](references/specification-audit.md).

The LLM autonomously runs targeted baseline/corrected-contract client verification
in a disposable checkout when it would help confirm a finding or validate a fix.
The report records actual diagnostics, fresh verification evidence and material
limitations; unexecuted clients are
labeled as proposals.

In `diff` and `pr` modes, findings must be caused by the reviewed commits. In `files`
mode, findings must be rooted in the named files or requested ranges. The wider
repository may be read as context in all modes.

## Safety and prerequisites

- Run the skill from the VOSTD repository with its Verus toolchain available.
- The working tree is treated as read-only. Only the requested report is written
  persistently; standalone proof experiments run in disposable locations.
  `pr` mode first fetches the review refs and switches the current checkout.
- Existing report files are preserved unless `--overwrite` is specified.
- Review assumes the change has already passed CI. Focused client comparisons run
  autonomously when useful and stay isolated; repository-wide verification is never repeated.

For the complete orchestration rules, evidence schema, and report format, see
[`SKILL.md`](SKILL.md). The aspect-specific reviewer instructions live in
[`personas/`](personas/); the workflow persona is conditional.
