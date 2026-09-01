---
name: vostd-guidelines-review
description: Review Verus code against VOSTD's coding guidelines (docs/coding-guidelines) and write a Markdown review file. Fans out one isolated reviewer per guideline aspect — maintainability, proof-engineering, workflow — verifies their claims by experiment where possible, consolidates the findings, and writes one severity-ranked English report.
---

# vostd-guidelines-review

Review code against VOSTD's coding guidelines
— the aspect-keyed pages under `docs/coding-guidelines/`
(`maintainability.md`, `proof-engineering.md`, `workflow.md`)
— and write one Markdown review file.
The review audits a whole target file (or set of files) as it stands at HEAD,
not a diff: the question is *which rules does this code follow and which does it violate*,
with each violation grounded in a cited rule and quoted evidence.

## Interface

```
<target[:lines] ...>  <output> [--overwrite] [--verify=<command>]
```

Wrap in double quotes any argument containing spaces.

- `<target[:lines] ...>` — **required**, one or more targets in the working tree.
  A target is a path, optionally narrowed `path:N-M,K-L` (1-based, inclusive);
  repeat a path to add ranges.
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
   Read the four guideline pages and every target file **in full** — the orchestrator
   needs them for synthesis, not just the personas. The guideline pages are read live
   at review time and are the authority for what to check: if they have changed since
   the personas were last edited, the pages win. Resolve the repository-context
   paths above and record the target's recent git history.

2. **Activate personas.**
   A persona runs unless the target *provably* contains nothing in its remit:
   - **maintainability, proof-engineering** — any target containing Verus constructs
     (`verus!`, `#[verus_verify]`, `#[verus_spec]`, `spec fn`, `proof fn`);
   - **workflow** — any target whose proof obligations carry solver configuration
     (`#[verus_verify(...)]` attributes, fuel, or broadcast groups).
   Activation is path-based and deterministic; do not triage with the model
   (a wrongly-skipped persona is a silent recall hole).

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

Launch all passes **in a single message** (parallel, isolated contexts).
Each pass prompt is built the same way:

1. the persona file's full text (`personas/<persona>.md`), verbatim, as the stable head;
2. the absolute paths of the repository-context table (guideline pages, vendored vstd,
   vstd_extra, verus binary, verify command, branch);
3. the target's full source.

Pass rules stated in every prompt:

- Read the full guideline page and the full target yourself; do not rely on summaries.
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
- You may run read-only commands (`git log`, grep, standalone verus experiments in
  `/tmp`). If an experiment touches repository files, back them up first, restore them
  byte-identical, and confirm `git status --porcelain` is empty.
- Exhaust the static checks first (reading, grep, git history); every experiment must
  be able to name the report outcome it can change — run none whose outcome changes
  nothing.
- Strip comments before any caller/usage scan of the repo, and state which apparent
  call sites were excluded as commented out.
- Time-box any live verification run to about eight minutes; never leave one half-run.
- Return findings as structured data (Findings / Compliance), not prose.

## Output format

One Markdown file:

```markdown
# Review: <target> (branch <branch>)

> Produced from docs/coding-guidelines; verification: <status line>.

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
- Read-only on the repository — the only file this skill writes is `<output>`.
