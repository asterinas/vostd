---
name: post-pr-review
description: Post a finished guidelines-review Markdown report to its GitHub PR as ONE review carrying all line-level comments, each anchored at a verified PR-head location (REQUEST_CHANGES when the posting account is not the PR author; COMMENT when it is — GitHub rejects authors requesting changes on their own PRs). Use after a review report (e.g. from vostd-code-review) exists and the user asks to raise it on the PR itself. Handles anchor verification, hunk eligibility, single-shot review creation, verification of landing, and post-submit fixes within GitHub's immutability limits.
---

# post-pr-review

Take a finished Markdown review report and land it on its GitHub PR as a single
`REQUEST_CHANGES` review whose findings are line-level comments at their anchors.

## Invariants (read first — each one was learned from a live failure)

1. **ONE review, ONE POST.** All line comments go out in a single
   `POST /repos/{o}/{r}/pulls/{n}/reviews` call (event + body + comments[]).
   A submitted review on GitHub is **frozen**: body PATCH → 404, review DELETE →
   422 `Can not delete a non-pending pull request review`, adding comments to it
   → 404, moving comments between reviews is impossible. Only the *comment
   bodies* stay editable (`PATCH /pulls/comments/{id}`, forever, own comments).
2. **Never "probe" with one comment first when more findings are queued.**
   The first submitted review can never absorb the rest — posting one as a test
   permanently splits the PR's review stream. If the user asks for a probe, state
   this consequence in one sentence and get explicit informed confirmation first;
   otherwise post the full set in one review.
3. **Attribution line (e.g. "Powered by … on behalf of @Marsman1996") goes in
   the review body only — never on the line comments.** The attribution always
   names the posting principal as `on behalf of @Marsman1996` (keep the `@`
   handle). That is the standing user ruling. (A stray PR-level comment to carry
   it is also forbidden; delete any already posted.)
4. **Outward-facing action: preview first.** Show the compact anchor table
   (file:line | type | one-line problem) and get the user's OK before the POST.
5. **Anchor authority = GitHub head SHA.** Resolve it via
   `gh api repos/{o}/{r}/pulls/{n}` → `head.sha` and compare with the SHA the
   report cites. Same SHA → cite directly. Different SHA → remap line numbers
   from the cited content to PR-head content with `git show <sha>:<path>` before
   anchoring, or refuse and ask.
6. **Every anchor must sit inside a diff hunk.** Fetch
   `gh api repos/{o}/{r}/pulls/{n}/files` and check the patch hunks for the
   target file. Added files: any line eligible. Context lines: eligible. Lines
   outside hunks (on unchanged side): not eligible — shift to the nearest
   in-hunk line.
7. **Never post review opinions about commits or comments/annotations.**
   Findings whose subject is a git commit (message style/content) or a code
   comment / doc-comment (completeness, ordering, wording polish) are NOT
   postable: the guidelines treat commit messages as intent-only evidence and
   documentation-completeness notes as at-most-mention-once compliance material,
   not findings. PR line comments carry source-anchored guideline violations
   only.
8. **No local-only artifacts in any GitHub-facing text** (user ruling, 2026-11-11,
   after `Details in the local report vostd-pr-909-review-2.md` went out in a
   review body). The review body and every line comment must be self-contained
   for a GitHub reader: never mention the local report's file name or path,
   working-tree paths, disposable draft directories, or any other local
   artifact. GitHub readers cannot open any of it — such pointers are dead text
   on the page. Report internals stay in the local report.

## Interface

```
post-pr-review <report.md> <PR-url-or-number>
```

The report is the review deliverable (scope line, findings with
`file:line` anchors, guideline kebab-names). Offline scratch drafts live under
`/tmp/` — never inside the repo working tree.

## Pipeline

1. **Parse.** Read the report in full; extract every finding: severity, guideline
   kebab-name, anchor path:line, 1–2 sentence problem. Apply invariant 7's
   exclusion first — drop any commit- or comment-subject item, even if the
   report lists it. Refuse on zero findings or on citation-SHA vs GitHub-head
   mismatch.
2. **Resolve & verify anchors.** Per invariant 5–6: resolve head SHA; for every
   anchor verify the cited bytes with `git show <head>:<path>` (match the quoted
   evidence); check hunk membership. Record the verification outcome; drop or
   fix anchors that fail.
3. **Draft offline.** Build the payload JSON under `/tmp/<slug>-pr<N>/`:
   `review.json` (event, short body, comments[]) plus per-comment drafts. Keep
   comments ultra-concise (format below). Print the preview table and **stop**
   for user confirmation.
4. **POST once.** Submit the review:

   ```bash
   gh api -X POST repos/{o}/{r}/pulls/{n}/reviews --input review.json
   ```

   The `event` field takes the endPoint enum value `"COMMENT"` — the state
   `COMMENTED` from the GET response is NOT a valid event (`422 Variable $event
   ... invalid value`).

   Comment object shape: `{"path": "<repo-relative>", "line": <int>, "body": "<text>"}`
   — **do NOT include `subject_type`** (rejected with 422
   `Field is not defined on DraftPullRequestReviewThread`). No `side` field:
   default is RIGHT (newfile). Use `--input <file>` from python or a file to
   avoid shell-quoting traps; `--raw-field` takes `key=value` as ONE argument
   (space-separated form yields `accepts 1 arg(s), received 2`).
5. **Verify landing.** The create-review response does NOT echo its comments.
   Run `gh api "repos/{o}/{r}/pulls/{n}/comments?per_page=100"` and check every
   comment's path/line; run `gh api repos/{o}/{r}/pulls/{n}/reviews` to confirm
   the state (`CHANGES_REQUESTED`, or `COMMENTED` for the own-PR COMMENT form)
   and review id/url. Only then report success.
6. **Report back.** Concise: review URL + the anchor table actually posted
   (path:line | type | one-line problem). Note any previously-flagged finding
   that was dropped at step 2 and why.

## Comment format (required)

```
**Type:** <guideline-kebab-name>
**Problem:** <1–2 sentences. Anchor numbers are against the PR head. Mention
sibling-site anchors in prose. One concrete fix pointer if short.>
```

Repo-language English; no fluff; no per-comment attribution (invariant 3).

## Review body (required)

The body is the PR's most visible text, and a submitted review's body is not
editable via API (invariant 1) — enforce concision at draft time. Hard cap:
2–3 sentences, one short paragraph, containing ONLY:

- what the review is (guidelines pass, scope in a few words);
- the list of finding types (kebab-names as they appear in the comments);
- the attribution line per invariant 3.

Never in the body: retracted candidates or their reasons, verification
process, persona activation, environment or CI disclosures, per-finding
detail, or any local-only artifact such as the local report's file name or
path (invariant 8). Those belong in the line comments (concise, per the format
above)
and in the local report. If a posted body is later judged too long, do not
retry the API — hand the user paste-ready replacement text for a manual
web-UI edit (invariant 1; no delete-and-repost).

## Post-submit fixes (the only ones that exist)

- `gh api -X PATCH repos/{o}/{r}/pulls/comments/{id} --input payload.json` —
  rewrite an own comment body (concision pass, anchor fix, attribution removal).
- `gh api -X DELETE repos/{o}/{r}/issues/comments/{id}` — remove a stray
  PR-level comment (own).
- Anything touching a submitted review itself (body edit, delete, un-submit,
  add comments) is impossible via API — say so rather than retrying, and route
  the user to the web UI / a repo-write user if they insist.

## Observed failure modes (do not re-diagnose from scratch)

| Symptom | Cause | Fix |
|---|---|---|
| POST reviews → 422 `subjectType ... not defined` | comment object carried `subject_type` | drop the field |
| create-review response shows `n_comments: 0` | response never embeds comments | verify via GET comments |
| PATCH review body → 404 | submitted reviews immutable | pending-only; none exists |
| PATCH review body with `--raw-field body <text>` → "accepts 1 arg(s)" | flag wants `key=value` | use `--input` file or `--raw-field key=value` |
| POST comment to reviews/{id}/comments → 404 | pending-only endpoint | cannot add after submit |
| DELETE review → 422 non-pending | submitted reviews undeletable | web UI only |
| POST reviews → 422 `Review Can not request changes on your own pull request` | the authenticated account is the PR author; GitHub forbids authors from REQUEST_CHANGES on their own PRs | land the identical payload with `"event": "COMMENT"` (single review, line comments unchanged); state the switch in the report-back |
| POST reviews with `"event": "COMMENTED"` → 422 `Variable $event ... invalid value` | `COMMENTED` is the state name, not the event enum value | use `"event": "COMMENT"` |
