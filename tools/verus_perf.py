#!/usr/bin/env python3
"""Parse Verus `--time-expanded` logs and compare two runs.

Usage:
    verus_perf.py parse  <log-file>                  # emit metrics JSON to stdout
    verus_perf.py compare <baseline.json> <new.json>  # emit markdown diff to stdout
    verus_perf.py to-bm <metrics.json> [-o out.json]  # emit github-action-benchmark
                                                      # custom JSON (rlimit series)

A `cargo dv verify --targets ostd -- --time-expanded` run consists of several
sequential Verus invocations. Each prints, per invocation:
    verification results:: <V> verified, <E> errors
    total-time:           <W> ms    (estimated total cpu time ...)
            total smt-run: <S> ms, <R> rlimit (<T> threads)
                1. <module>   <ms>, <rlimit>
                2. ...
We aggregate across all invocations (wall-times and smt-run/rlimit are
sequential-additive). rlimit is deterministic for a fixed build; wall-time has
run-to-run jitter.
"""

import json
import re
import sys


_RESULTS = re.compile(r"verification results::\s*(\d+)\s+verified,\s*(\d+)\s+errors")
_TOTAL_TIME = re.compile(r"^total-time:\s+(\d+)\s+ms")
_SMT_RUN = re.compile(r"total smt-run:\s+(\d+)\s+ms,\s*([\d,]+)\s+rlimit")
_MODULE = re.compile(r"^\s+\d+\.\s+(\S+)\s+(\d+)\s+ms,\s*([\d,]+)\s+rlimit")

# Per-module series emitted to the benchmark chart (charts get unwieldy beyond
# this; the full per-module breakdown still lives in `compare`).
_TOP_MODULES = 15


def parse(log_text):
    verified = errors = wall_ms = smt_run_ms = rlimit = 0
    modules = {}  # name -> {"smt_run_ms": int, "rlimit": int}

    lines = log_text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]

        m = _RESULTS.search(line)
        if m:
            verified += int(m.group(1))
            errors += int(m.group(2))

        m = _TOTAL_TIME.match(line)
        if m:
            wall_ms += int(m.group(1))

        m = _SMT_RUN.search(line)
        if m:
            smt_run_ms += int(m.group(1))
            rlimit += int(m.group(2).replace(",", ""))
            # Following indented "N. <module> <ms>, <rlimit>" lines are the
            # smt-run top modules for this invocation.
            j = i + 1
            while j < len(lines):
                mm = _MODULE.match(lines[j])
                if not mm:
                    break
                name = mm.group(1)
                ms2 = int(mm.group(2))
                rl2 = int(mm.group(3).replace(",", ""))
                cur = modules.setdefault(name, {"smt_run_ms": 0, "rlimit": 0})
                cur["smt_run_ms"] += ms2
                cur["rlimit"] += rl2
                j += 1
        i += 1

    return {
        "verified": verified,
        "errors": errors,
        "wall_ms": wall_ms,
        "smt_run_ms": smt_run_ms,
        "rlimit": rlimit,
        "modules": [
            {"name": n, "smt_run_ms": v["smt_run_ms"], "rlimit": v["rlimit"]}
            for n, v in sorted(modules.items(), key=lambda kv: -kv[1]["rlimit"])
        ],
    }


def to_benchmark(metrics):
    """Convert parsed metrics into github-action-benchmark `customSmallerIsBetter`
    entries. rlimit (deterministic) is the charted/alerted value; wall/smt-run
    (jittery) and counts ride in `extra` tooltips so timer jitter can't raise
    false alerts.
    """
    extra_total = (
        f"verified={metrics['verified']} errors={metrics['errors']} "
        f"smt-run={metrics['smt_run_ms']:,}ms wall={metrics['wall_ms']:,}ms"
    )
    entries = [
        {"name": "total rlimit", "unit": "rlimit", "value": metrics["rlimit"], "extra": extra_total}
    ]
    for m in metrics.get("modules", [])[:_TOP_MODULES]:
        entries.append(
            {
                "name": f"rlimit: {m['name']}",
                "unit": "rlimit",
                "value": m["rlimit"],
                "extra": f"smt-run={m['smt_run_ms']:,}ms",
            }
        )
    return entries


def _pct(new, old):
    return (new - old) / old * 100.0 if old else 0.0


def _signed(n):
    return f"{n:+,d}"


def compare(baseline, candidate):
    b, c = baseline, candidate
    out = []
    out.append("## Verus verification cost: `before` (previous main) vs `after` (new main)\n")
    out.append("| metric | before | after | Δ |")
    out.append("|---|---|---|---|")
    out.append(f"| verified | {b['verified']:,} | {c['verified']:,} | {_signed(c['verified'] - b['verified'])} |")
    out.append(f"| errors | {b['errors']} | {c['errors']} | {_signed(c['errors'] - b['errors'])} |")
    out.append(
        f"| total wall-time | {b['wall_ms']:,} ms | {c['wall_ms']:,} ms | "
        f"{_signed(c['wall_ms'] - b['wall_ms'])} ms ({_pct(c['wall_ms'], b['wall_ms']):+.1f}%) |"
    )
    out.append(
        f"| total smt-run | {b['smt_run_ms']:,} ms | {c['smt_run_ms']:,} ms | "
        f"{_signed(c['smt_run_ms'] - b['smt_run_ms'])} ms ({_pct(c['smt_run_ms'], b['smt_run_ms']):+.1f}%) |"
    )
    out.append(
        f"| **total rlimit** | {b['rlimit']:,} | {c['rlimit']:,} | "
        f"{_signed(c['rlimit'] - b['rlimit'])} ({_pct(c['rlimit'], b['rlimit']):+.1f}%) |"
    )

    # Correctness gate: the after run must have 0 errors and at least as many
    # verified items (no proofs dropped).
    if c["errors"] != 0:
        out.append("\n> ⚠️ **after run has verification errors** — cost comparison is moot until it verifies.")
    if c["verified"] < b["verified"]:
        out.append(
            f"\n> ⚠️ **verified count dropped** ({b['verified']} → {c['verified']}) — "
            "proofs may have been disabled/removed."
        )

    # Per-module rlimit delta (top by max(before, after)).
    bm = {x["name"]: x for x in b["modules"]}
    cm = {x["name"]: x for x in c["modules"]}
    rows = []
    for n in set(bm) | set(cm):
        br = bm.get(n, {"rlimit": 0, "smt_run_ms": 0})
        cr = cm.get(n, {"rlimit": 0, "smt_run_ms": 0})
        rows.append((n, br, cr))
    rows.sort(key=lambda r: -max(r[1]["rlimit"], r[2]["rlimit"]))

    out.append("\n### per-module smt-run rlimit (top 15)\n")
    out.append("| module | before rlimit | after rlimit | Δ rlimit |")
    out.append("|---|---|---|---|")
    for n, br, cr in rows[:15]:
        out.append(
            f"| `{n}` | {br['rlimit']:,} | {cr['rlimit']:,} | "
            f"{_signed(cr['rlimit'] - br['rlimit'])} ({_pct(cr['rlimit'], br['rlimit']):+.1f}%) |"
        )

    out.append(
        "\n\n> rlimit is deterministic across runs; wall-time / smt-run have "
        "run-to-run jitter. Negative rlimit = improvement."
    )
    return "\n".join(out)


def main(argv):
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    cmd = argv[1]
    if cmd == "parse":
        if len(argv) != 3:
            print("usage: verus_perf.py parse <log-file>", file=sys.stderr)
            return 2
        with open(argv[2], encoding="utf-8", errors="replace") as f:
            metrics = parse(f.read())
        json.dump(metrics, sys.stdout, indent=2)
        sys.stdout.write("\n")
        # Surface a fatal signal if verification had errors.
        return 0 if metrics["errors"] == 0 else 1
    if cmd == "compare":
        if len(argv) != 4:
            print("usage: verus_perf.py compare <baseline.json> <new.json>", file=sys.stderr)
            return 2
        with open(argv[2]) as f:
            baseline = json.load(f)
        with open(argv[3]) as f:
            candidate = json.load(f)
        print(compare(baseline, candidate))
        return 0
    if cmd == "to-bm":
        out_path = None
        positional = []
        args = argv[2:]
        i = 0
        while i < len(args):
            if args[i] == "-o" and i + 1 < len(args):
                out_path = args[i + 1]
                i += 2
            else:
                positional.append(args[i])
                i += 1
        if len(positional) != 1:
            print("usage: verus_perf.py to-bm <metrics.json> [-o <out>]", file=sys.stderr)
            return 2
        with open(positional[0]) as f:
            metrics = json.load(f)
        text = json.dumps(to_benchmark(metrics), indent=2)
        if out_path:
            with open(out_path, "w", encoding="utf-8") as f:
                f.write(text + "\n")
        else:
            print(text)
        return 0
    print(f"unknown command: {cmd}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
