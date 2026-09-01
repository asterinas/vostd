---
name: vostd-guidelines-review
description: Review Verus code against VOSTD's coding guidelines (docs/coding-guidelines) and write a Markdown review file. Fans out one isolated reviewer per guideline aspect — maintainability, proof-engineering, workflow — verifies their claims by experiment where possible, consolidates the findings, and writes one severity-ranked English report.
---

# vostd-guidelines-review

Review code against VOSTD's coding guidelines
— the aspect-keyed pages under `docs/coding-guidelines/`
(`maintainability.md`, `proof-engineering.md`, `workflow.md`)
— and write one Markdown review file.
The review audits the current working-tree bytes captured when the review starts,
including staged, unstaged, and untracked target content; it is not a diff review.
`HEAD` supplies branch and history context, not the reviewed source snapshot. The
question is *which rules does this code follow and which does it violate*, with each
violation grounded in a cited rule and quoted evidence.

## Interface

```
<target[:lines] ...>  <output> [--overwrite] [--verify=<command>]
```

Wrap in double quotes any argument containing spaces.

- `<target[:lines] ...>` — **required**, one or more targets in the working tree.
  A target is a path, optionally narrowed `path:N-M,K-L` (1-based, inclusive);
  repeat a path to add ranges. Ranges for the same path form a union. With no range,
  the whole file is in reporting scope. With ranges, read the whole file as context but
  report a finding only when its primary violating location intersects that union;
  out-of-range lines may be cited only as supporting context.
- `<output>` — **required, last positional** (`cp src... dest` style);
  refuse to overwrite unless `--overwrite`.
- `--verify=<command>` — the focused verification command used by the workflow aspect
  and the verification-experiment step (default: discover it from `AGENTS.md` / the
  `Makefile`; dv-based repos typically
  `cargo dv focus --targets <crate> -- --verify-only-module '<module-path>'`).
- `--overwrite` — replace the output file if it already exists.

## Repository context

Locate these once, before fanning out; the personas need the absolute paths:

| Item | How to locate |
|------|---------------|
| Guideline pages | `docs/coding-guidelines/{README,maintainability,proof-engineering,workflow}.md`. |
| Vendored vstd source | `grep '^vstd' Cargo.toml` (typical: `tools/verus/source/vstd`). |
| vstd_extra | `verified_libs/vstd_extra/` (external specs under `src/external/`). |
| Verus binary + Z3 | `tools/verus/source/target-verus/release/verus` and `tools/verus/source/z3` — used for standalone contract and rlimit experiments. |
| Verification gate | `AGENTS.md`, `Makefile`, `.github/workflows/`. |
| History rationale | `git log --follow -p -- <target>` / `git log --all -S '<string>'`. |

## Pipeline

Run these steps in order.

1. **Resolve the input.**
   Capture every target's current working-tree bytes and content hash once, before
   reading or fanning out. Store those bytes in dedicated snapshot files in a
   disposable directory outside the shared working tree, and use those immutable files
   throughout the review. Read every snapshot **in full** — the orchestrator needs it
   for synthesis, not just the personas. Do not silently switch to `HEAD` or refresh
   from a file that changes after capture; record the snapshot path and hash so the
   report identifies what was reviewed. Read the four guideline pages live at review
   start; they are the authority for what to check, so if they have changed since the
   personas were last edited, the pages win. Resolve the repository-context paths above
   and record the target's recent git history.

2. **Activate personas.**
   Activate all three personas for every Verus target. Do not skip the workflow
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
   it — re-read the cited code, check the named lemma signatures in vstd/vstd_extra,
   and re-run a persona's experiment only when the finding is pivotal (severity or a
   headline conclusion rides on it) or the reported result looks wrong. Assign a
   verdict:

   - **confirmed** — keep the finding unchanged.
   - **uncertain** — keep it, but prefix the problem line with `(unverified) `.
   - **refuted** — remove it, and list it under `## Retracted by verification` at the
     foot of the report with a one-line reason.

   Remove only on confident refutation; an unsure check is `uncertain`, not `refuted`.
   A finding also does not survive verification if the rule it cites no longer exists
   on the current guideline page — a method may propose, the page decides what counts
   as a violation.
   Cross-persona contradictions (two aspects claiming opposite facts about the same
   lines) are resolved here by running the more careful check — the winner's evidence
   decides. Record any such resolution in the report's addendum.

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
2. the absolute paths of the repository-context table (guideline pages, vendored vstd,
   vstd_extra, verus binary, verify command, branch);
3. each original target path plus its absolute snapshot path, content hash, and
   reporting ranges. Do not embed the target source in the prompt.

Pass rules stated in every prompt:

- Read the full guideline page and every snapshot file from the supplied paths; do not
  replace a snapshot with the original working-tree file or rely on summaries. Report
  locations using the original target path and snapshot line numbers, never the
  disposable snapshot path.
- Enforce reporting scope: a finding's primary violating location must intersect the
  target's requested range union. Lines outside it may support a scoped finding but
  cannot create an independent finding. Scope Compliance claims the same way.
- The guideline page outranks the persona file's own method list: enumerate the page's
  current rules and check every one — the persona's concerns are recipes for how to
  look, not the rule inventory.
- A method may only propose a finding; a finding stands only if a rule on the current
  page grounds it. If a page rule fits no method, design the check on the spot and
  keep the finding format.
- Re-measure repository constants at review time (e.g. the effective default rlimit,
  from the installed toolchain's `.verus-log/*.smt2` and `verifier.rs`); numbers
  written in a persona are hints, not facts.
- A finding exists only with quoted evidence — code lines, comment lines, command
  output, or named lemma/spec signatures checked in vstd/vstd_extra. State unknown
  facts as unknown.
- Cite every violation by the guideline's kebab-case short name
  (`docs/coding-guidelines/README.md`).
- Include a `Compliance` list of rules the code demonstrably follows, with line references.
- You may run read-only repository commands (`git log`, grep) and experiments in a
  disposable directory. Never edit, back up, or restore files in the shared working
  tree for an experiment. Before experimenting, record the live worktree status and
  hashes of every target; construct an isolated temporary copy or worktree that
  represents the exact reviewed snapshot, including relevant uncommitted target
  content. Run all intact and modified variants only there. If that snapshot cannot be
  reproduced safely, skip the experiment and report the premise as unknown. Afterwards,
  confirm that the live status and target hashes match their recorded values; they need
  not be clean.
- Exhaust the static checks first (reading, grep, git history); every experiment must
  be able to name the report outcome it can change — run none whose outcome changes
  nothing.
- In particular, do not run focused module verification merely because the workflow
  persona is active. Run it only under the workflow persona's stated conditions; when
  none holds, record that it was not run and why.
- Strip comments before any caller/usage scan of the repo, and state which apparent
  call sites were excluded as commented out.
- Time-box any live verification run to about eight minutes; never leave one half-run.
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
`Findings` or `Compliance`. Findings use a primary location inside the requested scope;
supporting out-of-range locations stay inside `quoted_evidence`. Do not assign the
orchestrator's `confirmed` / `uncertain` / `refuted` verdict in persona output.

## Output format

One Markdown file:

```markdown
# Review: <target> (branch <branch>)

> Produced from docs/coding-guidelines; verification: <status line>.
> Snapshot: working tree captured at review start; <target>=<content-hash> [<ranges>].

**Bottom line:** two to five sentences naming the single most important problem.

## High      (one `###` per finding)
## Medium    (one `###` per finding)
## Low       (one row per finding: Finding | Guideline | Detail)
## Compliance
## Suggested fix order
## Retracted by verification    (only if any)
## Addendum: cross-persona resolution    (only if any)
## Verification run record      (command, exit code, results, controlled variants)
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
