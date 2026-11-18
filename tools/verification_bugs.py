#!/usr/bin/env python3
"""Export the verification bug tracker to the dashboard."""

import json
import os
import re
import sys
from pathlib import Path
from urllib.request import Request, urlopen

TRACKER = "/repos/asterinas/vostd/issues/645"
ENTRY = re.compile(
    r"^[-*+][ \t]+!\[(fixed|confirmed|reported)\]"
    r"\(https://img\.shields\.io/[^)\n]+\)[ \t]*(\S.*)$",
    re.MULTILINE,
)
REFERENCE = re.compile(
    r"https://github\.com/(asterinas/[a-zA-Z0-9_.-]+)/(issues|pull)/(\d+)\b"
)
MARKDOWN_LINK = re.compile(r"\[([^\]]+)\]\((https://github\.com/[^)]+)\)")


def github_json(path):
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "vostd-dashboard"}
    if token := os.environ.get("GH_TOKEN"):
        headers["Authorization"] = f"Bearer {token}"
    with urlopen(Request("https://api.github.com" + path, headers=headers), timeout=10) as response:
        return json.load(response)


def collect_bugs(body):
    entries = []
    for status, description in ENTRY.findall(body):
        references = []
        for reference in REFERENCE.finditer(description):
            repo, kind, number = reference.groups()
            link = {"url": reference[0], "label": f"{repo.split('/')[1]}#{number}"}
            if link not in references:
                references.append(link)
        bare = REFERENCE.fullmatch(description.strip())
        if bare:
            repo, kind, number = bare.groups()
            endpoint = "pulls" if kind == "pull" else "issues"
            try:
                description = github_json(f"/repos/{repo}/{endpoint}/{number}")["title"]
            except (OSError, ValueError, KeyError):
                description = references[0]["label"]
        else:
            description = MARKDOWN_LINK.sub(r"\1", description)
            description = REFERENCE.sub(lambda ref: f"{ref[1].split('/')[1]}#{ref[3]}", description)
            description = description.replace("`", "")
        entries.append({"description": description, "status": status, "references": references})
    if not entries:
        raise ValueError("No tagged bug entries found in issue #645")
    return entries


if __name__ == "__main__":
    issue = github_json(TRACKER)
    bugs = collect_bugs(issue["body"])
    Path(sys.argv[1]).write_text(json.dumps(bugs, indent=2) + "\n", encoding="utf-8")
