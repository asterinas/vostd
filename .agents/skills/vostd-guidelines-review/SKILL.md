---
name: vostd-guidelines-review
description: Review a Git change or selected Verus files against VOSTD's coding guidelines (docs/coding-guidelines) and write a Markdown review file. Fans out one isolated reviewer per guideline aspect — maintainability, proof-engineering, workflow — verifies their claims by experiment where possible, and consolidates the findings into one severity-ranked English report.
---

# vostd-guidelines-review

Review a Git change or selected code against VOSTD's coding guidelines
— the aspect-keyed pages under `docs/coding-guidelines/`
(`maintainability.md`, `proof-engineering.md`, `workflow.md`)
— and write one Markdown review file. There are two modes, both anchored at the
current checkout (`HEAD`):

- **`diff <base>`** reviews the committed series
  `merge-base(<base>, HEAD)..HEAD`, oldest first. Each commit's message and diff are
  captured so its intent and code changes remain associated. Uncommitted edits are
  not reviewed in this mode.
- **`files <target[:lines] ...>`** reviews the current working-tree bytes of the
  named files, including staged, unstaged, and untracked target content.

To review a historical commit or range, check out its desired endpoint first so it
becomes `HEAD`. In either mode, the question is *which rules does this scoped code
follow and which does it violate*, with each violation grounded in a cited rule and
quoted evidence.

## Interface

```
diff   <base>               <output> [--overwrite]
files  <target[:lines] ...> <output> [--overwrite]
```

Wrap in double quotes any argument containing spaces.

- `diff` / `files` — **required first positional**, selecting the review mode.
- `<base>` — **required in `diff` mode**, any Git ref or SHA. Review
  `merge-base(<base>, HEAD)..HEAD`; `HEAD` is always the endpoint.
- `<target[:lines] ...>` — **required in `files` mode**, one or more targets in the
  working tree.
  A target is a path, optionally narrowed `path:N-M,K-L` (1-based, inclusive);
  repeat a path to add ranges. Ranges for the same path form a union. With no range,
  the whole file is in reporting scope. With ranges, read the whole file as context but
  report a finding only when its primary violating location intersects that union;
  out-of-range lines may be cited only as supporting context.
- `<output>` — **required, last positional** (`cp src... dest` style);
  refuse to overwrite unless `--overwrite`.
- `--overwrite` — replace the output file if it already exists.

## Repository context

Locate these once, before fanning out; the personas need the absolute paths:

| Item | How to locate |
|------|---------------|
| Guideline pages | `docs/coding-guidelines/{README,maintainability,proof-engineering,workflow}.md`. |
| Existing verified code | The entire vendored vstd tree located from `grep '^vstd' Cargo.toml` (typically `tools/verus/source/vstd`), all of `verified_libs/`, `ostd/specs/`, and Verus-bearing files under `ostd/src/`. |
| Verus binary + Z3 | `tools/verus/source/target-verus/release/verus` and `tools/verus/source/z3` — used for standalone contract experiments. |
| Verification gate | `AGENTS.md`, `Makefile`, `.github/workflows/`. |
| History rationale | `git log --follow -p -- <target>`. In `diff` mode, the captured commit series is the primary review input. |

## Pipeline

Run these steps in order.

1. **Resolve the input.**
   Resolve the mode first and capture one immutable review input in a disposable
   directory outside the shared working tree:

   - In `diff` mode, resolve and record `HEAD`, `<base>`, and their merge-base. Capture
     `git log --reverse -p --format=fuller <merge-base>..HEAD` so every commit message
     stays paired with its diff. Also record the commit IDs and changed paths. Refuse an
     empty series. Do not include staged, unstaged, or untracked edits.
   - In `files` mode, capture every target's current working-tree bytes and content hash
     once. Store each target in a dedicated snapshot file and record its requested range
     union.

   Use only these immutable inputs throughout the review. Read each input **in full**
   before fanning out; do not silently refresh it from a changing worktree. Read the
   four guideline pages live at review start; they are the authority for what to check,
   so if they have changed since the personas were last edited, the pages win. Resolve
   the repository-context paths above and record relevant earlier history.

2. **Activate personas.**
   Activate all three personas for every reviewed Verus path (changed paths in `diff`
   mode, named paths in `files` mode). Do not skip the workflow
   persona merely because the target has no solver knob: host coverage, upstream
   readiness, or toolchain configuration may still apply. Each persona first performs
   its cheap static applicability checks and records non-applicable rules as N/A with
   evidence. Persona activation does not by itself justify running verification or
   another expensive experiment.

3. **Fan out.**
   Spawn the persona passes (see *Spawning*): by default **one isolated agent per
   activated persona** — best recall. Each pass reads only its own persona block
   (selective exposure), reviews the target itself, and returns its findings as
   structured text under the *Evidence contract* below.

4. **Verify.**
   For each returned finding, isolate the key premise it rests on and try to **refute**
   it by re-reading the cited code and checking named lemma signatures in
   vstd/vstd_extra. Do not repeat persona experiments or run additional Verus
   verification in this step. Assign a verdict:

   - **confirmed** — keep the finding unchanged.
   - **uncertain** — keep it, but prefix the problem line with `(unverified) `.
   - **refuted** — remove it, and list it under `## Retracted by verification` at the
     foot of the report with a one-line reason.

   Remove only on confident refutation; an unsure check is `uncertain`, not `refuted`.
   A finding also does not survive verification if the rule it cites no longer exists
   on the current guideline page — a method may propose, the page decides what counts
   as a violation.
   Resolve cross-persona contradictions (two aspects claiming opposite facts about the
   same lines) from the stronger cited evidence. If static evidence cannot decide, keep
   the claim as `uncertain`; do not launch another experiment. Record the resolution in
   the report's addendum.

5. **Consolidate.**
   Merge findings that share one root cause into one entry carrying every violated
   rule's short name. Never drop a distinct guideline violation. Rank the survivors:
   `high` first, then `medium`, then `low`. Keep the *Compliance* section with the same
   rigor as the findings.

6. **Write the output.** (see *Output format*)

## Spawning a persona pass

Launch all passes **in a single message** (parallel) with a no-history isolated fork
(`fork_turns: "none"`, or the environment's exact equivalent). Do not use the default
conversation-inheriting fork: each pass receives only its persona and the explicit
context below.
Each pass prompt is built the same way:

1. the persona file's full text (`personas/<persona>.md`), verbatim, as the stable head;
2. the absolute paths of the repository-context table (guideline pages, existing
   verified-code roots, Verus binary, verification-gate configuration, branch);
3. the mode and its immutable review input: in `diff` mode, the absolute captured-log
   path, merge-base, HEAD, commit IDs, and changed paths; in `files` mode, each original
   target path plus its absolute snapshot path, content hash, and reporting ranges.
   Do not embed source or diff contents in the prompt.

Pass rules stated in every prompt:

- Read the full guideline page and immutable review input from the supplied paths; do
  not replace it with live Git output or working-tree files and do not rely on
  summaries. The live repository may be read only for surrounding context and
  verification. Report locations using original paths and source line numbers, never
  disposable paths.
- Enforce reporting scope. In `diff` mode, a finding's primary violating location must
  be introduced or materially changed by a reviewed commit; removed code may support a
  finding about the resulting change. In `files` mode, the primary location must
  intersect the target's requested range union. Context outside the scope cannot create
  an independent finding. Scope Compliance claims the same way.
- The guideline page outranks the persona file's own method list: enumerate the page's
  current rules and check every one — the persona's concerns are recipes for how to
  look, not the rule inventory.
- A method may only propose a finding; a finding stands only if a rule on the current
  page grounds it. If a page rule fits no method, design the check on the spot and
  keep the finding format.
- A finding exists only with quoted evidence — code lines, comment lines, command
  output, or named lemma/spec signatures checked in vstd/vstd_extra. State unknown
  facts as unknown.
- Cite every violation by the guideline's kebab-case short name
  (`docs/coding-guidelines/README.md`).
- Include a `Compliance` list of rules the code demonstrably follows, with line references.
- You may run read-only repository commands and standalone experiments in a disposable
  directory. Never edit, back up, restore, or construct modified variants of files in
  the shared working tree.
- Exhaust the static checks first (reading, grep, git history); every experiment must
  be able to name the report outcome it can change — run none whose outcome changes
  nothing.
- Do not run focused, module, repository-wide, or controlled-variant verification. Code
  accepted for review is assumed to have already passed CI. Standalone proof experiments
  used to check a specific logical premise are not CI verification and remain allowed.
- Return exactly the structured data defined by the *Evidence contract* below, with no
  surrounding prose.

## Evidence contract

Every persona returns one YAML-shaped block with exactly two top-level keys. Keep every
field; use `null` or `[]` rather than omitting an unknown or empty value.

```yaml
Findings:
  - id: <persona>-<stable-number>
    severity: high | medium | low
    guideline: <kebab-case-short-name>
    location: <original-target-path:line>
    quoted_evidence: <exact source, command output, or checked signature>
    problem: <one or two sentences>
    key_premise: <the factual claim the orchestrator should try to refute>
    experiment:
      attempted: true | false
      command: <exact command or null>
      exit_code: <integer or null>
      result: <what the result establishes, or why no experiment was run>
    suggestion: <concrete correction>
Compliance:
  - guideline: <kebab-case-short-name>
    status: complies | not-applicable
    locations: [<original-target-path:line>, ...]
    quoted_evidence: <exact supporting evidence or null>
    compliance_or_na_reason: <what is demonstrated, or why the rule does not apply>
```

Each current rule from the persona's guideline page appears at least once under either
`Findings` or `Compliance`. Findings use a primary location inside the requested diff
or file/range scope; out-of-scope support stays inside `quoted_evidence`. Commit
messages may establish intent but are not independently reviewed for style unless a
current VOSTD guideline explicitly requires it. Do not assign the orchestrator's
`confirmed` / `uncertain` / `refuted` verdict in persona output.

## Output format

One Markdown file:

```markdown
# Review: <diff-range-or-targets> (branch <branch>)

> Produced from docs/coding-guidelines; CI verification is a review precondition.
> Scope: <either `diff <merge-base>..<HEAD> [<commit IDs>]` or
> `files captured from the working tree; <target>=<content-hash> [<ranges>]`>.

**Bottom line:** two to five sentences naming the single most important problem.

## High      (one `###` per finding)
## Medium    (one `###` per finding)
## Low       (one row per finding: Finding | Guideline | Detail)
## Compliance
## Suggested fix order
## Retracted by verification    (only if any)
## Addendum: cross-persona resolution    (only if any)
## Evidence check record        (static checks and standalone logical experiments)
```

Every finding states: the guideline short-name, location (`file:line`), the quoted
evidence, the problem in one or two sentences, and a concrete suggestion.
Severity: `high` = a reviewer would block the PR on it;
`medium` = should be fixed before merge;
`low` = nit or readiness note.
The report is always in English.

## Ground rules

- The review stays delegated: one sub-agent per activated persona; the orchestrator
  synthesizes but does not review inline.
- Treat the existing working tree as read-only. The only persistent file this skill
  writes there is `<output>`; experiment artifacts belong in a disposable directory
  outside it and must not alter or restore user files.
