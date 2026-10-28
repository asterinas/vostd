#!/usr/bin/env python3
"""Generate VOSTD verification statistics for the GitHub Pages site.

The ``snapshot`` subcommand scans the VOSTD sources (``ostd/src`` and
``ostd/libs`` by default) with the Verus ``line_count`` tool and reports, per
module, how much executable code is verified, sits at a trusted boundary, or is
unverified. With ``--mainline-source`` (a checkout of the ``phaseII/mainline``
branch), each file's verified/trusted counts are clamped to the mainline
executable-LoC budget with the same normalization ``code_treemap.py`` applies,
so headline numbers describe real code size rather than post-rewrite growth.

The ``record`` subcommand appends a snapshot's totals to a history file (one
point per commit) that the site renders as a line chart.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LINE_COUNT = REPO_ROOT / "tools/verus/source/target-verus/release/line_count"
DEFAULT_SOURCES = ("src=ostd/src", "libs=ostd/libs")
DEFAULT_SPECS_SOURCE = "specs=ostd/specs"

VERIFIED = "verified_exec"
TRUSTED = "trusted"
UNVERIFIED = "unverified"
UNPLANNED = "unplanned"

TEST_DIRECTORY_NAMES = {"test", "tests"}

# Modules outside the verification plan, following code_treemap.py: their
# whole executable-LoC budget is drawn as unplanned and vostd counts are
# ignored for them.
UNPLANNED_ARCH_MODULES = {"boot", "iommu", "tdx_guest"}
UNPLANNED_LIBS = {"linux-bzimage", "ostd-macros", "ostd-test"}
# code_treemap.py's special case: vostd's align_ext is plain Rust, so its
# verified line count comes from this constant instead of line_count.
ALIGN_EXT_VERIFIED_EXEC = 24


@dataclass
class Coverage:
    """Classification counts for one module (or the whole tree)."""

    budget: int = 0  # executable LoC budget (mainline exec, or vostd exec if unmatched)
    verified_exec: int = 0
    trusted: int = 0
    unplanned: int = 0
    spec: int = 0
    proof: int = 0
    rust_mode: int = 0
    files: int = 0
    files_with_mainline: int = 0

    def add(self, other: "Coverage") -> None:
        for name in vars(self):
            setattr(self, name, getattr(self, name) + getattr(other, name))

    @property
    def total(self) -> int:
        return self.budget

    @property
    def unverified(self) -> int:
        return max(0, self.budget - self.verified_exec - self.trusted - self.unplanned)

    def as_dict(self) -> dict[str, Any]:
        return {
            "total": self.total,
            VERIFIED: self.verified_exec,
            TRUSTED: self.trusted,
            UNVERIFIED: self.unverified,
            UNPLANNED: self.unplanned,
            "spec": self.spec,
            "proof": self.proof,
            "rust_mode": self.rust_mode,
            "files": self.files,
            "files_with_mainline": self.files_with_mainline,
        }


def is_unplanned_module(group: str, child: str) -> bool:
    """Whether a module sits outside the verification plan (code_treemap.py)."""
    if group == "arch" and "/" in child:
        return child.split("/", 1)[1] in UNPLANNED_ARCH_MODULES
    return group == "libs" and child in UNPLANNED_LIBS


# --- Verified API extraction (rustdoc JSON) -------------------------------
# Ports kverus-dev's verus_cov.py + RustdocApiExtractor: an API is a function
# with a body in the published rustdoc that is neither spec/proof-only nor
# trusted away (external_body), excluding trait impls without bodies and
# auto-derived impl items.

SPEC_ONLY_ATTRS = (
    "#[verus::internal(spec)]",
    "#[verus::internal(proof)]",
    "#[verifier::when_used_as_spec(",
)
TRUSTED_ATTRS = {"#[verifier::external_body]"}
TRAIT_IMPL_NO_BODY_ATTRS = {"#[attr = Inline(Hint)]"}


def item_attr_strings(item: dict[str, Any]) -> list[str]:
    """Normalize rustdoc JSON attrs (plain strings or ``{"other": ...}``)."""
    strings = []
    for attr in item.get("attrs") or []:
        if isinstance(attr, dict):
            strings.append(str(attr.get("other", "")))
        else:
            strings.append(str(attr))
    return strings


def not_exec_code(item: dict[str, Any]) -> bool:
    """Spec/proof-only fns and items contributed from external spec files."""
    strings = item_attr_strings(item)
    if any(skip in attr for attr in strings for skip in SPEC_ONLY_ATTRS):
        return True
    filename = (item.get("span") or {}).get("filename", "")
    return "src/../specs" in filename or "/specs/" in filename


def not_verified(item: dict[str, Any]) -> bool:
    """Items trusted away entirely (external_body)."""
    return any(attr in TRUSTED_ATTRS for attr in item_attr_strings(item))


def is_trait_impl_without_body(item: dict[str, Any]) -> bool:
    return any(
        attr in TRAIT_IMPL_NO_BODY_ATTRS for attr in item_attr_strings(item)
    )


def is_automatically_derived_impl(item: dict[str, Any]) -> bool:
    return "automatically_derived" in item.get("attrs", [])


def trim_source_path(filename: str) -> str:
    """Make a rustdoc span filename repo-relative (starting at ``ostd/``)."""
    parts = Path(filename).parts
    for i, part in enumerate(parts):
        if part == "ostd":
            return Path(*parts[i:]).as_posix()
    return filename


def api_group(filename: str) -> str:
    """Bucket a rustdoc span filename into a coarse source group."""
    parts = Path(filename).parts
    for i, part in enumerate(parts):
        if part == "ostd" and i + 1 < len(parts):
            root, tail = parts[i + 1], parts[i + 2 :]
            if root == "libs" and tail:
                return f"libs/{tail[0]}"
            if root == "src" and tail and not tail[0].endswith(".rs"):
                if tail[0] == "arch" and len(tail) >= 2:
                    return f"arch/{tail[1]}"
                return tail[0]
            return root
    return (Path(filename).parent.as_posix() or ".")


def collect_verified_apis(doc_json_path: Path) -> tuple[int, list[dict[str, str]]]:
    """Verified APIs in a rustdoc JSON tree (``dv doc --json-output``).

    Returns the count plus one entry per API (qualified name, source group,
    location, documentation path) for the site's list view.
    """
    payload = json.loads(Path(doc_json_path).read_text(encoding="utf-8"))
    index = payload.get("index", {})
    if not isinstance(index, dict):
        return 0, []

    # Canonical rustdoc paths handle re-exports and types defined in other modules.
    paths = {str(key): value for key, value in payload.get("paths", {}).items()}
    module_paths: dict[str, list[str]] = {}

    def visit_module(item_id: str, path: list[str]) -> None:
        item = index.get(str(item_id), {})
        module = (item.get("inner") or {}).get("module")
        if module is None or str(item_id) in module_paths:
            return
        module_paths[str(item_id)] = path
        for child_id in module.get("items", []):
            child = index.get(str(child_id), {})
            child_name = child.get("name")
            if not child_name:
                continue
            child_path = path + [child_name]
            kind = next(iter(child.get("inner") or {}), "")
            paths.setdefault(str(child_id), {"path": child_path, "kind": kind})
            if kind == "module":
                visit_module(str(child_id), child_path)

    root_id = str(payload.get("root", ""))
    visit_module(root_id, [index.get(root_id, {}).get("name") or "ostd"])

    def doc_path(item_id: str) -> str | None:
        summary = paths.get(str(item_id), {})
        path = summary.get("path", [])
        kind = summary.get("kind")
        prefixes = {"struct": "struct", "enum": "enum", "union": "union",
                    "trait": "trait", "type_alias": "type", "function": "fn",
                    "primitive": "primitive"}
        if not path or kind not in prefixes:
            return None
        return "/".join(path[:-1] + [f"{prefixes[kind]}.{path[-1]}.html"])

    derived_ids: set[str] = set()
    owner_names: dict[str, str] = {}
    owner_docs: dict[str, str] = {}
    for item in index.values():
        impl_info = (item.get("inner") or {}).get("impl")
        if not impl_info:
            continue
        if is_automatically_derived_impl(item):
            derived_ids.update(impl_info.get("items", []))
        for_info = impl_info.get("for")
        if not isinstance(for_info, dict):
            continue
        owner = None
        resolved = for_info.get("resolved_path")
        if isinstance(resolved, dict):
            owner = resolved.get("path")
        elif isinstance(for_info.get("primitive"), str):
            owner = for_info["primitive"]
        elif isinstance(for_info.get("slice"), dict):
            element = for_info["slice"]
            owner = f"[{element.get('primitive') or element.get('generic') or '_'}]"
        if owner:
            for item_id in impl_info.get("items", []):
                owner_names[str(item_id)] = owner
                if isinstance(resolved, dict):
                    owner_path = doc_path(str(resolved.get("id")))
                    if owner_path:
                        owner_docs[str(item_id)] = owner_path

    # Default trait methods live on the trait page rather than an impl page.
    for item_id, item in index.items():
        trait = (item.get("inner") or {}).get("trait")
        if trait is not None:
            for child_id in trait.get("items", []):
                owner_names[str(child_id)] = item.get("name", "")
                if path := doc_path(str(item_id)):
                    owner_docs[str(child_id)] = path

    entries: list[dict[str, str]] = []
    for item in index.values():
        name = item.get("name")
        if name is None:
            continue
        span = item.get("span") or {}
        if not span:
            continue
        function_info = (item.get("inner") or {}).get("function")
        if not function_info or function_info.get("has_body") is False:
            continue
        if item.get("id") in derived_ids:
            continue
        if str(name).isupper():
            continue
        if not_exec_code(item) or not_verified(item):
            continue
        if is_trait_impl_without_body(item):
            continue

        item_id = str(item.get("id"))
        owner = owner_names.get(item_id)
        qualified = str(name)
        if owner:
            qualified = f"{owner}::{name}"
        url = doc_path(item_id)
        if item_id in owner_docs:
            url = f"{owner_docs[item_id]}#method.{name}"
        # Foreign-type impls have no local type page. Link to the exact body in
        # Verusdoc's source view instead of a nonexistent alloc/core HTML page.
        if not url or not url.startswith(f"{index.get(root_id, {}).get('name') or 'ostd'}/"):
            source = trim_source_path(span.get("filename", ""))
            if source.startswith("ostd/src/"):
                start = span.get("begin", [0])[0]
                end = span.get("end", [start])[0]
                url = f"src/ostd/{source.removeprefix('ostd/src/')}.html#{start}-{end}"
        entries.append(
            {
                **({"doc_path": url} if url else {}),
                "name": qualified,
                "group": api_group(span.get("filename", "")),
                "location": f'{trim_source_path(span.get("filename", ""))}:'
                f'{span.get("begin", [0, 0])[0]}:{span.get("begin", [0, 0])[1]}',
            }
        )
    entries.sort(key=lambda e: (e["location"], e["name"]))
    return len(entries), entries


def is_test_source(relative: Path) -> bool:
    parts = [part.casefold() for part in relative.parts]
    filename = parts[-1] if parts else ""
    stem = Path(filename).stem.casefold()
    return (
        stem in TEST_DIRECTORY_NAMES
        or any(part in TEST_DIRECTORY_NAMES for part in parts)
        or stem.endswith(("_test", "_tests"))
    )


def run_line_count_file(
    line_count_path: Path, file_path: Path, *, no_external_by_default: bool = False
) -> tuple[dict[str, Any] | None, str | None]:
    """Run Verus line_count on one source file and parse its JSON report."""
    cmd = [str(line_count_path), str(file_path), "--json"]
    if no_external_by_default:
        cmd.append("--no-external-by-default")

    result = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or "unknown error"
        return None, f"{file_path}: {detail.splitlines()[-1]}"
    try:
        return json.loads(result.stdout), None
    except json.JSONDecodeError as exc:
        return None, f"{file_path}: invalid line_count JSON: {exc}"


def classify_lines(report: dict[str, Any] | None) -> dict[str, int]:
    """Bucket a line_count ``total`` map into VOSTD's verification statuses.

    ``total`` maps a comma-joined kind set (``"exec,trusted"``, ``"proof,exec"``,
    ``""`` for Rust-mode code outside ``verus!``, ...) to a line count. The
    buckets follow ``code_treemap.py``: any set containing ``trusted`` is
    trusted, then ``exec`` (including ``proof,exec`` proof blocks living in
    exec functions), ``spec``, ``proof``, and the empty set is Rust-mode.
    Comments, layout, and directives are ignored.
    """
    counts = {name: 0 for name in (VERIFIED, TRUSTED, "spec", "proof", "rust_mode")}
    if report is None:
        return counts
    for labels, value in report.get("total", {}).items():
        kinds = {part.strip().lower() for part in labels.split(",") if part.strip()}
        if "trusted" in kinds:
            counts[TRUSTED] += int(value or 0)
        elif "exec" in kinds:
            counts[VERIFIED] += int(value or 0)
        elif "spec" in kinds:
            counts["spec"] += int(value or 0)
        elif "proof" in kinds:
            counts["proof"] += int(value or 0)
        elif not kinds:
            counts["rust_mode"] += int(value or 0)
    return counts


def mainline_budget(buckets: dict[str, int]) -> int:
    """Executable-LoC budget of a mainline file (no VOSTD twin counted here).

    Mainline files are plain Rust run through ``--no-external-by-default``, so
    function bodies land in the ``exec`` kind (verified bucket here); blank
    lines and item shells stay unaccounted. ``code_treemap.py`` counts the same
    ``exec`` kind set as its per-file budget.
    """
    return buckets[VERIFIED] + buckets[TRUSTED]


def normalize_coverage(total: int, full: int, partial: int) -> tuple[int, int]:
    """Clamp VOSTD counts to the mainline executable-LoC budget.

    Mirrors ``code_treemap.py``: the full:partial ratio is preserved, scaled
    down when rewrites inflate the VOSTD tree past the mainline file verifies.
    """
    total = max(0, int(total))
    full = max(0, int(full))
    partial = max(0, int(partial))
    verified_total = full + partial
    if verified_total > total and verified_total > 0:
        exact_full = total * full / verified_total
        full = int(exact_full)
        partial = total - full
        if exact_full - full >= 0.5 and partial > 0:
            full += 1
            partial -= 1
    return full, partial


def module_path(relative: Path, kind: str) -> tuple[str, str] | None:
    """Map a source file relative to its root to a (group, child) module pair.

    ``src`` files under ``arch/<platform>/...`` group under ``arch`` with the
    platform retained in the child name; other ``src`` files group by top-level
    directory. ``libs`` files roll up under ``libs`` with the crate as child.
    """
    parts = relative.parts
    if not parts:
        return None
    if kind == "libs":
        return "libs", parts[0]

    if parts[0] == "arch" and len(parts) >= 3:
        tail = parts[2:]
        child = Path(tail[0]).stem if len(tail) == 1 else tail[0]
        return "arch", f"{parts[1]}/{child}"

    if len(parts) == 1:
        return relative.stem, relative.stem

    tail = parts[1:]
    child = Path(tail[0]).stem if len(tail) == 1 else tail[0]
    return parts[0], child


def parse_exclude(specs: list[str]) -> set[tuple[str, str | None]]:
    """Parse ``--exclude`` specs into (group, child|None) pairs."""
    parsed: set[tuple[str, str | None]] = set()
    for spec in specs:
        spec = spec.strip().strip("/")
        if not spec:
            continue
        if "/" in spec:
            group, child = spec.split("/", 1)
            if group.strip() and child.strip():
                parsed.add((group.strip().strip("/"), child.strip().strip("/")))
        else:
            parsed.add((spec, None))
    return parsed


def is_excluded(group: str, child: str, excluded: set[tuple[str, str | None]]) -> bool:
    """Check exclusion for group/child including arch platform prefixes."""
    if (group, child) in excluded or (group, None) in excluded:
        return True
    if group == "arch" and "/" in child:
        platform, module = child.split("/", 1)
        return (
            ("arch", platform) in excluded
            or (platform, None) in excluded
            or (platform, module) in excluded
        )
    return False


def inventory(roots: list[tuple[str, Path]]) -> dict[tuple[str, Path], Path]:
    """Collect ``{(kind, relative_path): absolute_path}`` for a tree's roots."""
    files: dict[tuple[str, Path], Path] = {}
    for kind, root in roots:
        for file in sorted(root.rglob("*.rs"), key=lambda p: str(p)):
            relative = file.relative_to(root)
            if not is_test_source(relative):
                files[(kind, relative)] = file
    return files


def collect_coverage(
    line_count_path: Path,
    vostd_roots: list[tuple[str, Path]],
    mainline_roots: list[tuple[str, Path]] | None,
    jobs: int,
    excluded: set[tuple[str, str | None]],
) -> tuple[dict[str, dict[str, Coverage]], list[str]]:
    """Count every file, pairing each VOSTD file with its mainline twin."""
    if mainline_roots is None:
        mainline_roots = []

    vostd_files = inventory(vostd_roots)
    mainline_files = inventory(mainline_roots)

    vostd_reports: dict[tuple[str, Path], dict[str, Any] | None] = {}
    mainline_reports: dict[tuple[str, Path], dict[str, Any] | None] = {}
    warnings: list[str] = []

    with ThreadPoolExecutor(max_workers=jobs) as pool:
        # VOSTD files are counted verbatim (external-by-default, as
        # code_treemap.py counts its verified tree).
        for (key, report, error) in [
            (key, *run_line_count_file(line_count_path, path))
            for key, path in sorted(vostd_files.items())
        ]:
            vostd_reports[key] = report
            if error:
                warnings.append(error)
        # Mainline files are plain Rust; --no-external-by-default makes foreign
        # items count as exec instead of being trusted away.
        for (key, report, error) in [
            (key, *run_line_count_file(line_count_path, path, no_external_by_default=True))
            for key, path in sorted(mainline_files.items())
        ]:
            mainline_reports[key] = report
            if error:
                warnings.append(error)

    modules: dict[str, dict[str, Coverage]] = {}

    def account(group: str, child: str, coverage: Coverage) -> None:
        if is_excluded(group, child, excluded):
            return
        modules.setdefault(group, {}).setdefault(child, Coverage())
        modules[group][child].add(coverage)

    for key in sorted(vostd_reports):
        group_child = module_path(key[1], key[0])
        if group_child is None:
            continue
        group, child = group_child

        buckets = classify_lines(vostd_reports[key])
        has_mainline = key in mainline_reports
        if has_mainline:
            budget = mainline_budget(classify_lines(mainline_reports[key]))
            if child == "align_ext" and group == "libs":
                # code_treemap.py: vostd's align_ext is pure Rust, use the
                # constant instead of the empty line_count report.
                full, partial = normalize_coverage(
                    budget, ALIGN_EXT_VERIFIED_EXEC, buckets[TRUSTED]
                )
            else:
                full, partial = normalize_coverage(
                    budget, buckets[VERIFIED], buckets[TRUSTED]
                )
        else:
            # No mainline twin (new/rewritten file) and not on the unplanned
            # list: treat as unverified, matching code_treemap.py's "missing
            # vostd counterpart" semantics.
            budget = buckets[VERIFIED] + buckets[TRUSTED]
            full, partial = 0, 0

        unplanned = 0
        if is_unplanned_module(group, child):
            # Outside the verification plan: the whole budget is unplanned.
            unplanned, full, partial = budget, 0, 0

        account(
            group,
            child,
            Coverage(
                budget=budget,
                verified_exec=full,
                trusted=partial,
                unplanned=unplanned,
                spec=buckets["spec"],
                proof=buckets["proof"],
                rust_mode=buckets["rust_mode"],
                files=1,
                files_with_mainline=1 if has_mainline else 0,
            ),
        )

    # Mainline-only files: entirely unverified, still sized by their budget.
    for key in sorted(mainline_reports):
        if key in vostd_files:
            continue
        group_child = module_path(key[1], key[0])
        if group_child is None:
            continue
        group, child = group_child
        budget = mainline_budget(classify_lines(mainline_reports[key]))
        account(group, child, Coverage(budget=budget, files=1))

    return modules, warnings


def totals_of(modules: dict[str, dict[str, Coverage]]) -> Coverage:
    totals = Coverage()
    for children in modules.values():
        for coverage in children.values():
            totals.add(coverage)
    return totals


def count_spec_proof(
    line_count_path: Path, root: Path, jobs: int
) -> tuple[int, int, int]:
    """Spec/proof line totals for a spec-library tree (e.g. ``ostd/specs``).

    These files hold only spec/proof code (no exec), so they never contribute
    to the executable-LoC budget or the treemap; they are added to the
    line-chart totals as ``spec_all``/``proof_all``.
    """
    spec = proof = files = 0
    warnings: list[str] = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for report, error in [
            run_line_count_file(line_count_path, path, no_external_by_default=True)
            for path in sorted(root.rglob("*.rs"), key=lambda p: str(p))
            if not is_test_source(path.relative_to(root))
        ]:
            if error:
                warnings.append(error)
                continue
            buckets = classify_lines(report)
            spec += buckets["spec"]
            proof += buckets["proof"]
            files += 1
    if warnings:
        for warning in warnings[:10]:
            print(warning, file=sys.stderr)
    return spec, proof, files


def git_output(repo: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, text=True, check=False
    )
    return result.stdout.strip() if result.returncode == 0 else ""


def print_report(modules: dict[str, dict[str, Coverage]], warnings: list[str]) -> None:
    totals = totals_of(modules)
    print(f"Files scanned: {totals.files}")
    if totals.files:
        matched = totals.files_with_mainline
        print(f"Files with a mainline twin: {matched} ({100 * matched / totals.files:.1f}%)")
    print(f"Executable LoC (mainline budget): {totals.total:,}")
    for label, value in (
        ("Verified", totals.verified_exec),
        ("Trusted boundary", totals.trusted),
        ("Unverified", totals.unverified),
        ("Unplanned", totals.unplanned),
        ("Spec", totals.spec),
        ("Proof", totals.proof),
        ("Rust-mode (vostd raw)", totals.rust_mode),
    ):
        share = 100 * value / totals.total if totals.total else 0
        print(f"{label:<22} {value:>8,}  {share:>6.1f}%")
    print()
    print(
        f"{'Module':<12} {'Exec LoC':>10} {'Verified':>9} "
        f"{'Trusted':>8} {'Unverified':>11} {'Backed':>7}"
    )
    for group in sorted(modules):
        coverage = Coverage()
        for child_coverage in modules[group].values():
            coverage.add(child_coverage)
        backed = (
            f"{100 * coverage.files_with_mainline / coverage.files:.0f}%"
            if coverage.files
            else "-"
        )
        total = coverage.total or 1
        print(
            f"{group:<12} {coverage.total:>10,} "
            f"{100 * coverage.verified_exec / total:>8.1f}% "
            f"{100 * coverage.trusted / total:>7.1f}% "
            f"{100 * coverage.unverified / total:>10.1f}% "
            f"{backed:>7}"
        )
    if warnings:
        print(f"\nline_count warnings/errors: {len(warnings)}", file=sys.stderr)
        for warning in warnings[:10]:
            print(f"  {warning}", file=sys.stderr)
        if len(warnings) > 10:
            print(f"  ... and {len(warnings) - 10} more", file=sys.stderr)


def write_snapshot(
    modules: dict[str, dict[str, Coverage]],
    output: Path,
    sha: str,
    date: str,
    mainline_sha: str | None,
    specs: tuple[int, int, int] | None = None,
    verified_apis: int | None = None,
    api_entries: list[dict[str, str]] | None = None,
) -> None:
    totals = totals_of(modules)
    totals_dict = totals.as_dict()
    if specs is not None:
        spec, proof, _ = specs
        # Line-chart totals: spec/proof across src+libs+specs. The plain
        # spec/proof keys stay src+libs-only (they must sum over modules).
        totals_dict["spec_all"] = totals.spec + spec
        totals_dict["proof_all"] = totals.proof + proof
    if verified_apis is not None:
        totals_dict["verified_apis"] = verified_apis
    snapshot = {
        "date": date,
        "sha": sha,
        "mainline_sha": mainline_sha,
        "modules": [
            {"group": group, "child": child, **coverage.as_dict()}
            for group, children in sorted(modules.items())
            for child, coverage in sorted(children.items())
            if coverage.total > 0
        ],
        "totals": totals_dict,
    }
    if api_entries is not None:
        snapshot["verified_apis_list"] = api_entries
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(snapshot, indent=2) + "\n", encoding="utf-8")
    print(f"Snapshot: {output}")


def resolve_roots(specs: list[str]) -> list[tuple[str, Path]]:
    """Resolve 'src=DIR' / 'libs=DIR' specs to (kind, absolute dir) pairs."""
    roots = []
    for spec in specs:
        kind, sep, path = spec.partition("=")
        if kind not in ("src", "libs"):
            kind, path = "src", spec
        root = Path(path).expanduser()
        if not root.is_absolute():
            root = REPO_ROOT / root
        root = root.resolve()
        if not root.is_dir():
            raise SystemExit(f"source directory does not exist: {root}")
        roots.append((kind, root))
    return roots


def cmd_snapshot(args: argparse.Namespace) -> int:
    line_count_path = args.line_count.expanduser().resolve()
    if not line_count_path.is_file():
        raise SystemExit(
            f"line_count does not exist: {line_count_path}\n"
            "Build it with: cd tools/verus/source && cargo build --release -p line_count"
        )

    modules, warnings = collect_coverage(
        line_count_path,
        resolve_roots(args.source or list(DEFAULT_SOURCES)),
        resolve_roots(args.mainline_source) if args.mainline_source else None,
        args.jobs,
        parse_exclude(args.exclude),
    )

    if args.arch is not None and "arch" in modules:
        modules["arch"] = {
            child: coverage
            for child, coverage in modules["arch"].items()
            if child.startswith(f"{args.arch}/")
        }
        if not modules["arch"]:
            del modules["arch"]

    if not modules:
        raise SystemExit("line_count produced no executable lines")

    specs = None
    if args.specs_source:
        specs_root = Path(args.specs_source).expanduser()
        if not specs_root.is_absolute():
            specs_root = REPO_ROOT / specs_root
        specs_root = specs_root.resolve()
        if specs_root.is_dir():
            specs = count_spec_proof(line_count_path, specs_root, args.jobs)
            print(f"Spec library: {specs[2]} files, spec {specs[0]:,}, proof {specs[1]:,}")

    verified_apis = None
    api_entries: list[dict[str, str]] | None = None
    if args.doc_json:
        doc_json = Path(args.doc_json).expanduser()
        if not doc_json.is_absolute():
            doc_json = Path.cwd() / doc_json
        if doc_json.is_file():
            verified_apis, api_entries = collect_verified_apis(doc_json)
            print(f"Verified APIs: {verified_apis:,}")
        else:
            print(f"warning: rustdoc JSON not found, skipping API count: {doc_json}",
                  file=sys.stderr)

    sha = args.sha or git_output(REPO_ROOT, "rev-parse", "HEAD")
    date = args.date or git_output(REPO_ROOT, "show", "-s", "--format=%cI", sha) or ""
    write_snapshot(modules, args.output, sha, date, args.mainline_sha, specs,
                   verified_apis, api_entries)
    print_report(modules, warnings)
    return 0


def cmd_record(args: argparse.Namespace) -> int:
    snapshot = json.loads(Path(args.snapshot).read_text(encoding="utf-8"))
    history_path = Path(args.history)
    history_path.parent.mkdir(parents=True, exist_ok=True)
    if history_path.is_file():
        history = json.loads(history_path.read_text(encoding="utf-8"))
    else:
        history = {"points": []}
    points = history.setdefault("points", [])

    totals = snapshot["totals"]
    # History points chart the widest spec/proof scope (src+libs+specs);
    # fall back to the legacy module-scope keys for older snapshots.
    keys = ("total", VERIFIED, TRUSTED, UNVERIFIED, UNPLANNED, "rust_mode")
    point = {
        "date": snapshot["date"],
        "sha": snapshot["sha"],
        **{key: totals[key] for key in keys},
        "spec": totals.get("spec_all", totals["spec"]),
        "proof": totals.get("proof_all", totals["proof"]),
    }
    if "verified_apis" in totals:
        point["verified_apis"] = totals["verified_apis"]
    for existing in points:
        if existing.get("sha") == point["sha"]:
            existing.update(point)  # reruns refresh the same commit
            break
    else:
        points.append(point)
    points.sort(key=lambda p: (p.get("date") or "", p.get("sha") or ""))

    history_path.write_text(json.dumps(history, indent=2) + "\n", encoding="utf-8")
    print(f"History now holds {len(points)} points: {history_path}")
    return 0


def positive_integer(value: str) -> int:
    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return parsed


def parse_args() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    snapshot = subparsers.add_parser("snapshot", help="count verification status per module")
    snapshot.add_argument(
        "--line-count", type=Path, default=DEFAULT_LINE_COUNT, help="Verus line_count binary"
    )
    snapshot.add_argument(
        "--source",
        action="append",
        default=[],
        metavar="KIND=DIR",
        help="source root as 'src=DIR' or 'libs=DIR'; repeatable "
        f"(default: {' '.join(DEFAULT_SOURCES)})",
    )
    snapshot.add_argument(
        "--mainline-source",
        action="append",
        default=[],
        metavar="KIND=DIR",
        help="mainline baseline roots; repeatable (checkout of phaseII/mainline)",
    )
    snapshot.add_argument(
        "--specs-source",
        default="ostd/specs",
        help="spec-library tree folded into the line-chart spec/proof totals "
        "(spec_all/proof_all); does not appear in the treemap",
    )
    snapshot.add_argument(
        "--doc-json",
        help="rustdoc JSON tree (cargo dv doc --package ostd --json-output) "
        "counted into totals.verified_apis",
    )
    snapshot.add_argument("--mainline-sha", help="commit the mainline checkout is at")
    snapshot.add_argument("--arch", help="keep only one arch platform, e.g. x86")
    snapshot.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="exclude 'group/child' or 'group' from stats; repeatable",
    )
    snapshot.add_argument("--sha", help="commit being counted (default: git HEAD)")
    snapshot.add_argument("--date", help="ISO timestamp of the commit (default: from git)")
    snapshot.add_argument("-o", "--output", type=Path, default=Path("stats-snapshot.json"))
    snapshot.add_argument("--jobs", type=positive_integer, default=min(8, os.cpu_count() or 1))
    snapshot.set_defaults(func=cmd_snapshot)

    record = subparsers.add_parser("record", help="append snapshot totals to a history file")
    record.add_argument("--snapshot", type=Path, required=True)
    record.add_argument("--history", type=Path, required=True)
    record.set_defaults(func=cmd_record)

    return parser


def main(argv: list[str] | None = None) -> int:
    args = parse_args().parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
