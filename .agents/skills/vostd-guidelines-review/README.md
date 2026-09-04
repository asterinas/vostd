# VOSTD Guidelines Review

`vostd-guidelines-review` reviews either a Git change or selected Verus source
files against the VOSTD coding guidelines and writes a single, evidence-backed
Markdown report. It covers the maintainability and proof-engineering aspects, plus
two conditional workflow checks, in
[`docs/coding-guidelines`](../../../docs/coding-guidelines/README.md).

## Usage

The skill has two modes, both anchored at the current checkout (`HEAD`):

```text
$vostd-guidelines-review diff <base> <output> [--overwrite]
$vostd-guidelines-review files <target[:lines] ...> <output> [--overwrite]
```

Examples:

```text
$vostd-guidelines-review diff main review.md
$vostd-guidelines-review diff origin/main review.md --overwrite
$vostd-guidelines-review files ostd/src/sync/rwlock.rs review.md
$vostd-guidelines-review files ostd/src/sync/rwlock.rs:120-240 review.md
```

`diff <base>` reviews the committed series
`merge-base(<base>, HEAD)..HEAD`, oldest first. Each commit's message and diff
are captured together so reviewers can judge the code against that commit's
intent. Uncommitted changes are excluded. To review a historical endpoint,
check it out first so it becomes `HEAD`.

`files` reviews the current working-tree contents of the named files, including
staged, unstaged, and untracked target content. Targets use 1-based inclusive
line ranges. Repeat a path to review multiple ranges from the same file. If no
range is supplied, the whole file is in scope.

In both modes, the output path is the final positional argument and is not
overwritten unless `--overwrite` is present.

## What the review does

The skill:

1. snapshots the commit series or current working-tree target contents;
2. runs isolated reviews for maintainability and proof engineering;
3. runs a workflow review only when an `rlimit` changes or a `std`/`core`/`alloc`
   external specification is newly added or materially changed;
4. checks important claims against the source, the complete active `vstd`, and existing
   verified code throughout VOSTD;
5. consolidates the results by severity; and
6. writes an English Markdown report containing findings, compliant rules,
   suggested fix order, and evidence-check details.

The workflow pass checks only whether a changed rlimit exceeds `200` and whether a
newly added or materially changed project-local external specification for a
`std`/`core`/`alloc` API should be proposed upstream. It does not review CI or host
coverage, toolchain configuration, solver stability, proof decomposition, or other
workflow concerns.

In `diff` mode, findings must be caused by the reviewed commits. In `files`
mode, findings must be rooted in the named files or requested ranges. The wider
repository may be read as context in both modes.

## Safety and prerequisites

- Run the skill from the VOSTD repository with its Verus toolchain available.
- The working tree is treated as read-only. Only the requested report is written
  persistently; standalone proof experiments run in disposable locations.
- Existing report files are preserved unless `--overwrite` is specified.
- Review assumes the change has already passed CI and does not repeat focused or
  repository-wide verification.

For the complete orchestration rules, evidence schema, and report format, see
[`SKILL.md`](SKILL.md). The aspect-specific reviewer instructions live in
[`personas/`](personas/); the workflow persona is conditional.
