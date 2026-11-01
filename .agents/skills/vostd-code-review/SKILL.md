---
name: vostd-code-review
description: Review a GitHub PR, Git change or selected Verus files for VOSTD coding guidelines and API specification quality. PR mode checks out the PR head and compares it with upstream main. Checks maintainability, proof engineering and API contracts, with targeted isolated caller experiments; workflow checks cover only rlimit caps and upstreamable std/core/alloc external specs.
---

# vostd-code-review

Review a Git change or selected code against VOSTD's coding guidelines
— primarily `maintainability.md` and `proof-engineering.md`, with two narrowly
scoped checks from `workflow.md`, plus API-contract criteria in
`personas/specification.md`
— and write one Markdown review file. There are three modes:

- **`pr <pr-link>`** fetches upstream `main` and the PR head, switches the current
  repository to that head, then reviews `merge-base(main, HEAD)..HEAD` using the
  same committed-series pipeline as `diff`.
- **`diff <base>`** reviews the committed series
  `merge-base(<base>, HEAD)..HEAD`, oldest first. Each commit's message and diff are
  captured so its intent and code changes remain associated. Uncommitted edits are
  not reviewed in this mode.
- **`files <target[:lines] ...>`** reviews the current working-tree bytes of the
  named files, including staged, unstaged, and untracked target content.

In `diff` and `files`, the current checkout (`HEAD`) is the anchor. To review a
historical commit or range with `diff`, check out its desired endpoint first.
In every mode, the question is *which rules does this scoped code
follow and which does it violate*, and *can a caller use the API as documented*,
with each violation grounded in a cited guideline or API check and quoted evidence.

## Interface

```
diff   [<base>]             <output> [--overwrite]
files  <target[:lines] ...> <output> [--overwrite]
pr     <pr-link>            <output> [--overwrite]
```

In `diff` mode, `<base>` is optional. When it is omitted the review uses the default base
`origin/main` — the `main` branch of the upstream repository
(https://github.com/asterinas/vostd, remote `origin`). One positional after `diff` is the
`<output>` with `<base>` defaulted; two positionals are `<base>` then `<output>`.

Wrap in double quotes any argument containing spaces.

- `diff` / `files` / `pr` — **required first positional**, selecting the review mode.
- `<pr-link>` — **required in `pr` mode**; a GitHub pull request URL for the current
  repository's upstream, normally `https://github.com/asterinas/vostd/pull/<number>`.
  This mode fetches and switches the checkout before reviewing against upstream
  `main`, including when the PR's declared target is another branch.
- `<base>` — **optional in `diff` mode**; any Git ref or SHA. When omitted, defaults to
  `origin/main` (the upstream https://github.com/asterinas/vostd `main`, remote `origin`). Review
  `merge-base(<base>, HEAD)..HEAD`; `HEAD` is always the endpoint. Run `git fetch origin`
  first to review against the latest upstream main; the skill resolves `origin/main` to its
  current local value without fetching. `pr` mode fetches its own main and head refs.
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

The LLM starts with source review and autonomously runs isolated client/contract
experiments when their results could change a finding or validate its correction.
See `references/specification-audit.md` for the procedure.

## Repository context

Locate these once, before fanning out; the personas need the absolute paths:

| Item | How to locate |
|------|---------------|
| Guideline pages | `docs/coding-guidelines/{README,maintainability,proof-engineering,workflow}.md`, plus `proof-patterns.md` as supporting (non-mandatory) examples. The workflow reviewer uses only `decompose-before-raising-rlimit`'s numeric cap and `upstream-reusable-specs`. |
| Existing verified code | The entire vendored vstd tree located from `grep '^vstd' Cargo.toml` (typically `tools/verus/source/vstd`), all of `verified_libs/`, `ostd/specs/`, and Verus-bearing files under `ostd/src/`. |
| Verus binary + Z3 | `tools/verus/source/target-verus/release/verus` and `tools/verus/source/z3`, present after `make verus`/`cargo dv bootstrap`; used for standalone logical experiments and isolated spec-client checks when useful. |
| Spec audit procedure | `references/specification-audit.md` relative to this skill; API contract analysis and client experiment isolation. |
| History rationale | `git log --follow -p -- <target>`. In `diff` and `pr` modes, the captured commit series is the primary review input. |
| Default diff base | `diff`: local `origin/main`, without fetching. `pr`: freshly fetched `refs/heads/main` from the URL's upstream repository, independent of local remote names. |

## Pipeline

Run these steps in order.

1. **Resolve the input.**
   Resolve the mode first and capture one immutable review input in a disposable
   directory outside the shared working tree:

   - In `pr` mode, perform the checkout procedure below first, then capture the
     committed series exactly as in `diff`, using the fetched main SHA as `<base>`.
     Preserve the PR URL, number, declared target, starting branch/SHA, fetched main
     SHA and checked-out head SHA in the review metadata. Use the recorded SHAs
     throughout; later PR updates do not change this review's input.
   - In `diff` mode, default `<base>` to `origin/main` (the upstream
     https://github.com/asterinas/vostd `main` branch) when omitted, resolve it to its current
     local SHA without fetching, then record `HEAD`, `<base>`, and their merge-base. Capture
     `git log --reverse -p --format=fuller <merge-base>..HEAD` so every commit message
     stays paired with its diff. Also record the commit IDs and changed paths. Refuse an
     empty series. Do not include staged, unstaged, or untracked edits.
   - In `files` mode, capture every target's current working-tree bytes and content hash
     once. Store each target in a dedicated snapshot file and record its requested range
     union.

   Use only these immutable inputs throughout the review. Read each input **in full**
   before fanning out; do not silently refresh it from a changing worktree. Read the
   `README.md`, `maintainability.md`, and `proof-engineering.md` live at review start;
   they are the authority for those review aspects. Read only the two permitted
   sections of `workflow.md`: the `200` rlimit cap under
   `decompose-before-raising-rlimit` and `upstream-reusable-specs`. Resolve the
   repository-context paths above and record relevant earlier history.

2. **Activate personas.**
   Activate the maintainability and proof-engineering personas for every reviewed
   Verus path. Activate the Specification persona when reporting scope contains an
   exec/proof API, its contract, or an API newly brought under verification. Include
   private helpers feeding that API; no `pub` requirement. The Specification persona
   decides whether targeted experiments would help confirm a finding or correction.
   Activate the workflow persona only when the
   immutable review input has at least one of these changes in reporting scope:

   - an added, removed, or changed `#[verifier::rlimit(...)]`; or
   - a newly added or materially changed external specification for a `std`, `core`,
     or `alloc` API. A material change affects the specified API, contract, model, or
     panic/unwind semantics; formatting, imports, and comments alone are not material.

   In `files` mode, determine whether the target changed by comparing its captured
   bytes with `HEAD` (treat an untracked file as wholly added). If neither condition
   applies, do not launch the workflow persona and do not report workflow Compliance
   or N/A entries. Persona activation alone does not justify verification or another
   expensive experiment; each experiment needs a concrete question whose answer
   could change the review conclusion or validate a suggested correction.

3. **Fan out.**
   Spawn the persona passes (see *Spawning*): by default **one isolated agent per
   activated persona** — best recall. Each pass reads only its own persona block
   (selective exposure), reviews the target itself, and returns its findings as
   structured text under the *Evidence contract* below.
   If all activated passes exceed the available agent slots, queue the remaining
   pass until a slot is free; retain isolated persona contexts.

4. **Verify.**
   For each returned finding, isolate the key premise it rests on and try to **refute**
   it by re-reading the cited code and checking named lemma signatures in
   vstd/vstd_extra. Check the suggested correction too: resolve its receiver, argument
   types, trait bounds, and Verus modes, and compare its logical conditions with the
   original. A valid concern with an invalid fix needs a corrected suggestion; it does
   not justify retracting the concern or publishing the invalid fix. Do not repeat
   persona experiments or run additional Verus verification in this step. Assign a verdict:

   - **confirmed** — keep the finding unchanged.
   - **uncertain** — keep it, but prefix the problem line with `(unverified) `.
   - **refuted** — remove it, and list it under `## Retracted by verification` at the
     foot of the report with a one-line reason.

   Remove only on confident refutation; an unsure check is `uncertain`, not `refuted`.
   A guideline finding also does not survive verification if its rule no longer exists
   on the current guideline page. The Specification persona's `api-preconditions`
   and `api-postconditions` checks are separately defined by this skill and do not
   require a matching coding-guideline entry.
   Resolve cross-persona contradictions (two aspects claiming opposite facts about the
   same lines) from the stronger cited evidence. If static evidence cannot decide, keep
   the claim as `uncertain`; do not launch another experiment. Record the resolution in
   the report's addendum.

5. **Consolidate.**
   Merge findings that share one root cause into one entry carrying every violated
   rule's short name. Never drop a distinct guideline violation. Rank the survivors:
   `high` first, then `medium`, then `low`. Use internal `Compliance` records to
   check review coverage; omit them from the final report.

6. **Write the output.** (see *Output format*)

## PR checkout

1. Validate the URL and confirm its repository matches this checkout's upstream
   using remote URLs and GitHub PR metadata. Retrieve the PR head SHA and declared
   target, for example with `gh api repos/<owner>/<repo>/pulls/<number>`. Check the
   output overwrite policy before switching. Record the starting branch and SHA,
   and copy this skill directory to the disposable input directory so its personas
   and references remain available after checkout.
2. Check staged and unstaged tracked changes and any in-progress merge/rebase.
   If any are present, stop and report the affected paths or operation so the PR
   review uses clean source. Preserve local changes and untracked files; do not stash, reset, clean
   or force checkout automatically.
3. Fetch `refs/heads/main` and `refs/pull/<number>/head` directly from the validated
   upstream URL into dedicated local refs such as
   `refs/codex/review-pr/<number>/main` and `refs/codex/review-pr/<number>/head`.
   GitHub's PR head ref supports fork PRs without adding a contributor remote.
   Resolve both refs to commit SHAs and confirm the fetched head matches the PR
   metadata; if the PR changed during retrieval, refresh metadata and fetch once
   more, then report any remaining mismatch rather than reviewing an unknown head.
4. Run `git switch --detach <head-sha>` in the current repository. Let Git's normal
   overwrite checks protect untracked paths; if switching fails, report the error
   and leave those files intact. Confirm `HEAD` equals the recorded PR head and
   compute `git merge-base <main-sha> <head-sha>`. Fetch missing history if a shallow
   checkout prevents resolving that merge-base; report unresolved failures.
5. Continue the diff pipeline using those immutable SHAs. Read project guidelines
   and surrounding source from the PR checkout; use the captured copy of this skill
   for orchestration. Leave the checkout at the reviewed PR head and state that
   head and the main SHA in the report and completion message.

## Spawning a persona pass

Launch passes in parallel up to available capacity with a no-history isolated fork
(`fork_turns: "none"`, or the environment's exact equivalent). Do not use the default
conversation-inheriting fork: each pass receives only its persona and the explicit
context below.
Each pass prompt is built the same way:

1. the persona file's full text (`personas/<persona>.md`), verbatim, as the stable head;
2. the absolute paths of the repository-context table (guideline pages, existing
   verified-code roots, Verus binary, verification-gate configuration, branch);
3. the mode and immutable review input: in `diff` or `pr` mode,
   the absolute captured-log path, merge-base, HEAD, commit IDs, and changed paths;
   in `files` mode, each original target path plus its absolute snapshot path,
   content hash, and reporting ranges.
   Do not embed source or diff contents in the prompt.

Pass rules stated in every prompt:

- Read the immutable review input from the supplied paths; do not replace it with live
  Git output or working-tree files and do not rely on summaries. Maintainability and
  proof-engineering reviewers read their full guideline page; the workflow reviewer
  reads only the two permitted rule sections named in its persona. The Specification
  reviewer reads its own criteria and the linked audit procedure, plus its named
  supporting guideline sections. The live repository
  may be read only for surrounding context and verification. Report locations using
  original paths and source line numbers, never disposable paths.
- Enforce reporting scope. In `diff` or `pr` mode, a finding's primary violating location must
  be introduced or materially changed by a reviewed commit; removed code may support a
  finding about the resulting change. Bringing a previously unverified API under
  verification counts as a material change even if its body is unchanged: cite the
  original API location and the changed enclosing macro/attribute as scope evidence.
  In `files` mode, the primary location must
  intersect the target's requested range union. Context outside the scope cannot create
  an independent finding. Scope Compliance claims the same way.
- For maintainability and proof engineering, the guideline page outranks the persona
  file's method list: enumerate and check every current rule. The workflow persona is
  the explicit exception: check only the triggered `rlimit > 200` condition and/or
  whether a newly added or materially changed `std`/`core`/`alloc` external spec
  should be proposed upstream. Do not inspect or report any other workflow concern.
- The Specification persona is another focused exception: check its two API criteria
  rather than enumerating a full guideline page. Its findings may cite the skill-defined
  `api-preconditions` or `api-postconditions` IDs.
- A method may only propose a finding; a finding stands only if a permitted guideline
  or the Specification persona's API criteria ground it. For maintainability and
  proof engineering, if a page rule fits no method, design the check on the spot and
  keep the finding format.
- Apply guidelines within Rust/Verus semantics. A style rule cannot justify weakening
  a contract, adding an unsupported trait bound, or assuming a type invariant for an
  arbitrary spec value. If guideline wording would require such a change, record the
  guideline ambiguity in the evidence check record rather than reporting that change
  as a required fix.
- Check each concrete suggestion against the actual signature and original logical
  conditions. In particular, `x matches Some(v) ==> P(v)` accepts `None`; preserve any
  existing `x is Some` requirement. Resolve the receiver that owns a reused predicate
  and distinguish `P` from `Option<P>` before suggesting a replacement. Distinguish a
  demonstrated violation from a valid concern whose proposed fix needs correction.
- A finding exists only with quoted evidence — code lines, comment lines, command
  output, or named lemma/spec signatures checked in vstd/vstd_extra. State unknown
  facts as unknown.
- Cite every violation by the guideline's kebab-case short name
  (`docs/coding-guidelines/README.md`) or one of the two explicit API check IDs.
- Classify a finding by its suggested action. A finding whose
  correction is to write or reword documentation or comments
  (`document-verified-apis`, `document-real-proof-debt`) is
  reportable only when the missing or wrong text would mislead a
  reviewer about verified behavior or a trust boundary — a missing
  or contradicting trusted-boundary/`Safety` statement for a newly
  introduced verified API, or a doc claim inconsistent with the
  contract. Completeness-only documentation findings — enumerating
  trivial clauses the signature or ordinary rustdoc already states,
  bullets not
  mirroring every conjunct, retrofitting a module-level paragraph
  onto code whose verification grew in the diff, wording or format
  polish — are not findings; mention them at most once under
  `Compliance`. A reportable documentation finding is always
  `low`.
- Include a `Compliance` list of rules the code demonstrably follows, with line references.
- You may run read-only repository commands and standalone experiments in a disposable
  directory. Never edit, back up, restore, or construct modified variants of files in
  the shared working tree.
- Exhaust the static checks first (reading, grep, git history); every experiment must
  be able to name the report outcome it can change — run none whose outcome changes
  nothing.
- Do not repeat CI verification. Standalone proof experiments checking a specific
  logical premise remain allowed. The only focused/module or controlled-variant
  exception is the Specification persona's autonomous targeted experiments, following
  `references/specification-audit.md` in a disposable checkout. Repository-wide
  verification remains excluded, and no experiment may edit the shared working tree.
- Return exactly the structured data defined by the *Evidence contract* below, with no
  surrounding prose.

## Evidence contract

Every persona returns one YAML-shaped block with exactly two keys: `Findings` and
`Compliance`. `Compliance` is an internal review-coverage record. Keep every field;
use `null` or `[]` rather than omitting an unknown or empty value.

```yaml
Findings:
  - id: <persona>-<stable-number>
    severity: high | medium | low
    guideline: <kebab-case-guideline-name or api-preconditions or api-postconditions>
    location: <original-target-path:line>
    quoted_evidence: <exact source, command output, or checked signature>
    problem: <one or two sentences>
    key_premise: <the factual claim the orchestrator should try to refute>
    experiment:
      attempted: true | false
      command: <exact command or null>
      exit_code: <integer or null>
      result: <what the result establishes, or null if no experiment was run>
    suggestion: <concrete correction>
Compliance:
  - guideline: <kebab-case-guideline-name or api-preconditions or api-postconditions>
    status: complies | not-applicable
    locations: [<original-target-path:line>, ...]
    quoted_evidence: <exact supporting evidence or null>
    compliance_or_na_reason: <what is demonstrated, or why the rule does not apply>
```

For Specification, cover both API check IDs under `Findings` or `Compliance`.
For maintainability and proof engineering, each current rule from the persona's
guideline page appears at least once under either `Findings` or `Compliance` —
a rule with no violation appears under `Compliance` only; never surface a
manufactured finding to clear the list. For
workflow, include only the applicable triggered check(s); omit all non-triggered and
all other workflow rules rather than recording N/A entries. Findings use a primary
location inside the requested diff or file/range scope; out-of-scope support stays
inside `quoted_evidence`. Commit messages may establish intent but are not independently
reviewed for style unless a current VOSTD guideline explicitly requires it. Do not
assign the orchestrator's `confirmed` / `uncertain` / `refuted` verdict in persona
output.

## Output format

One Markdown file:

```markdown
# Review: <diff-range-or-targets> (branch <branch>)

> Produced from docs/coding-guidelines and the skill's API-contract criteria;
> CI verification is a review precondition.
> Scope: <`pr <URL> main=<SHA> head=<SHA> merge-base=<SHA> [<commit IDs>]`,
> `diff <merge-base>..<HEAD> [<commit IDs>]`, or
> `files captured from the working tree; <target>=<content-hash> [<ranges>]`>.

**Bottom line:** two to five sentences naming the single most important problem.

## High      (one `###` per finding)
## Medium    (one `###` per finding)
## Low       (one row per finding: Finding | Guideline | Detail;
             merge rows sharing one guideline and root cause)
## Retracted by verification    (only if any)
## Addendum: cross-persona resolution    (only if any)
## Evidence check record        (static, standalone and targeted spec-client evidence)
```

Every finding states: the guideline short-name or API check ID, location (`file:line`),
the quoted evidence, the problem in one or two sentences, and a concrete suggestion.
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
  In `pr` mode, the PR checkout step additionally fetches review refs and switches
  `HEAD` as described above; the review itself remains read-only.
