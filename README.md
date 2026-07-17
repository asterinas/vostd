# Formal Verification of Asterinas OSTD with Verus

[![docs](https://img.shields.io/badge/docs-vostd-blue)](https://asterinas.github.io/vostd/)
[![verify](https://img.shields.io/github/actions/workflow/status/asterinas/vostd/ci.yml?branch=main&label=verify)](https://github.com/asterinas/vostd/actions/workflows/ci.yml)
[![verify (verus-lang/verus)](https://img.shields.io/github/actions/workflow/status/asterinas/vostd/ci-upstream-verus.yml?branch=main&label=verify%20(verus-lang%2Fverus))](https://github.com/asterinas/vostd/actions/workflows/ci-upstream-verus.yml)

## Overview

The `vostd` project provides a formally-verified version of [OSTD](https://asterinas.github.io/book/ostd/index.html), the (unofficial) standard library for OS development in safe Rust. OSTD encapsulates low-level hardware interactions—which require `unsafe` Rust—into a small set of high-level, safe abstractions, enabling complex, general-purpose OSes like [Asterinas](https://github.com/asterinas/asterinas) to be written entirely in safe Rust. By design, OSTD guarantees *soundness*: no undefined behavior is possible regardless of how its API is used. The goal of `vostd` is to bolster this soundness through formal verification with [Verus](https://github.com/verus-lang/verus).

This work is ongoing. Our current focus is OSTD's *memory management* and *synchronization* subsystems—core components directly tied to kernel memory safety—and we aim to extend verification to further parts of OSTD over time.

## Publications

This project is tied to the following papers:

- 🏆 **CortenMM** — *CortenMM: Efficient Memory Management with Strong Correctness Guarantees*, SOSP 2025 (Best Paper). Concurrency proofs for OSTD memory management; for the artifact see the [`func-correct`](https://github.com/asterinas/vostd/tree/func-correct) branch and [TELOS-syslab/CortenMM-Artifact](https://github.com/TELOS-syslab/CortenMM-Artifact). [paper](https://dl.acm.org/doi/10.1145/3731569.3764836)
- **KVerus** — *KVerus: Scalable and Resilient Formal Verification Proof Generation for Rust Code*, ASE 2026 (Industry Track). Retrieval-augmented, self-adaptive proof synthesis and repair for Verus. Upstream-accepted proofs in OSTD `AI-assist`; see [these PRs](https://github.com/asterinas/vostd/pulls?q=is%3Apr+label%3AAI-assist+). [paper](https://arxiv.org/abs/2605.03822)
- **Beyond Benchmarks** — *Beyond Benchmarks: A Case Study of LLM-Generated Verus Specification Failures on Asterinas Vostd*, ASE 2026 (Industry Track). *coming soon*

## Bugs Found by Verification

Formal verification has surfaced real bugs in OSTD and the upstream Asterinas kernel—undefined behavior, deadlocks, arithmetic overflows, counter wraparound, and reachable `debug_assert`s. We track them in [issue #645](https://github.com/asterinas/vostd/issues/645).

## Project Structure

- `ostd/src/`: OSTD implementation and proofs.
- `ostd/specs/`: Verus specifications.
- `verified_libs/`: auxiliary verified libraries (e.g. `vstd_extra`).
- `dv`: the build system (xtask-equivalent).

## Building

### Prerequisites

- [Install Rust](https://www.rust-lang.org/tools/install).
- Initialize submodules (for our [custom build tool](https://github.com/asterinas/rust-deductive-verifier)):

  ```bash
  git submodule update --init --recursive
  ```

### Build Verus

```bash
make verus      # or: cargo dv bootstrap
```

Verus is cloned and built under `tools/verus`. If the download fails, clone it manually into `tools/verus` and re-run `cargo dv bootstrap`.

> [!NOTE]
> We use our [own fork](https://github.com/asterinas/verus) of Verus, kept in sync with upstream. To build against upstream Verus instead, use `cargo dv bootstrap --upstream-verus` (our CI tracks upstream; breaking changes are usually resolved within about a week).

> [!TIP]
> If Verus is already installed elsewhere and you only want to reproduce a verification result (not the recommended way to set up the project), point `CARGO_VERUS_PATH` at the directory containing the `cargo-verus` binary (or add it to your `PATH`) and run `cargo verus verify`.

### Verify

```bash
make                                         # verify everything (or: cargo dv verify)
cargo dv verify -f --targets ostd            # ostd only, skip dependencies
cargo dv verify --targets vstd_extra         # the verified dependency crate
```

### Clean

```bash
make clean      # or: cargo dv clean          # remove build artifacts for a fresh build
```

### Build & Docs

```bash
make build      # or: cargo dv build               # build the verification targets
make doc        # or: cargo dv doc --target ostd   # generate API docs at doc/index.html
```

The generated documentation can be found at `doc/`.
An [online version](https://asterinas.github.io/vostd/) is also available.

### IDE Support

- VSCode: [`verus-analyzer`](https://marketplace.visualstudio.com/items?itemName=verus-lang.verus-analyzer)
- Emacs: [`verus-mode`](https://github.com/verus-lang/verus-mode.el)

## Contributing

We welcome your contributions! Conventions:

- Prefix `axiom fn` with `axiom_`, `proof fn` with `lemma_`, and proof helpers that manipulate `tracked` linear permission objects with `tracked_`.
- Prefer associated functions over isolated lemmas.
- Put specifications and lemmas in `ostd/specs`; general definitions and lemmas in `verified_libs/vstd_extra`.
- Before submitting: run `make verus-upgrade` (`cargo dv bootstrap --upgrade`) to follow the [latest supported Verus](https://github.com/asterinas/verus), and `make fmt` (`cargo dv fmt`) to format (enforced).
- For Verus changes, prefer PRs to [the upstream repo](https://github.com/verus-lang/verus) over our fork, since we aim to minimize differences between them.
