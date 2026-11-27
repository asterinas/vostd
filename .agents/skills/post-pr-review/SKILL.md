---
name: post-pr-review
description: Publish a finished VOSTD guidelines-review Markdown report to its GitHub PR as one review with verified inline comments. Use when the user asks to post the report on the PR.
---

# Post a PR review

Use the finished report and PR URL or number. Keep drafts in a unique directory under `/tmp`.

## Prepare and preview

1. Extract each finding's guideline kebab-name, source anchor, and evidence. Exclude findings about commits and about comment or doc-comment wording, completeness, or ordering.
2. Get the PR head SHA and author login from `gh api repos/{o}/{r}/pulls/{n}`. Verify the evidence with `git show <head>:<path>`. If the report cites an older SHA, remap by matching its evidence to the head and confirm the finding still applies. Paginate the PR files and verify each anchor is on the right side of a diff hunk, including eligible context lines. Move an anchor only when the new line still identifies the same issue. Record exclusions and reasons. Stop if no eligible findings remain.
3. Compare `gh api user --jq .login` with the PR author. Use `COMMENT` on your own PR and `REQUEST_CHANGES` otherwise.
4. Draft the JSON payload with `commit_id` set to the verified head, plus `event`, `body`, and `comments`. Show the PR, SHA, event, body, anchor table (file:line | type | problem), and any exclusions. Get the user's approval before posting. Refresh the preview and approval if the head, posting account, or payload changes.

## Write the review

Use concise English and make all text self-contained for GitHub readers. Omit local report names, filesystem paths, and draft details.

Keep the body to one short paragraph of at most three sentences. Include only the review scope, finding types, and an attribution sentence naming the tool, model, and GitHub handle of the person on whose behalf the review is posted. Use this form: `Automated VOSTD guidelines review by <tool> (<model>) on behalf of @<GitHub handle>.` For example: `Automated VOSTD guidelines review by Codex (GPT-6.2-Sol) on behalf of @Marsman1996.`

Use the tool and model that produced the review. If the tool, model, or represented person's GitHub handle is unknown, ask the user for the missing values before showing the final preview. The authenticated account used to post the review may differ from the person named in the attribution. Place attribution only in the review body.

Use this inline format, mentioning relevant sibling anchors and a short fix pointer when useful.

```markdown
**Type:** <guideline-kebab-name>
**Problem:** <concrete issue in one or two sentences>
```

## Submit and verify

- Recheck the head and posting account before sending the approved payload. Send every comment in one request. For right-side anchors, use comment objects containing `path`, `line`, and `body`, omitting `subject_type`. Avoid probe reviews and separate PR-level comments.

  ```bash
  gh api -X POST repos/{o}/{r}/pulls/{n}/reviews --input review.json
  ```

- If the POST outcome is uncertain, inspect the PR for a matching review by account, commit, body, and comments. Stop if the outcome remains uncertain. After a confirmed rejection, fix the cause and follow the preview rule if the payload changes.
- Verify the returned review ID using `GET /repos/{o}/{r}/pulls/{n}/reviews/{id}` and the paginated `GET /repos/{o}/{r}/pulls/{n}/reviews/{id}/comments`. Check the commit, state (`COMMENTED` or `CHANGES_REQUESTED`), and all comment bodies and original anchors. Report the review URL, posted anchor table, and exclusions with reasons.

## Correct a posted review

For authorized text edits, use `PUT /repos/{o}/{r}/pulls/{n}/reviews/{id}` for the review body and `PATCH /repos/{o}/{r}/pulls/comments/{id}` for an inline comment body. Verify each edit. A text edit leaves the anchor and review membership in place. GitHub's review deletion endpoint applies to pending reviews. Get authorization before any additional post or deletion needed for a correction.
