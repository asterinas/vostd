# Formal Verification of Asterinas OSTD with Verus

[![docs](https://img.shields.io/badge/docs-vostd-blue)](https://asterinas.github.io/vostd/)
[![verify](https://img.shields.io/github/actions/workflow/status/asterinas/vostd/ci.yml?branch=main&label=verify)](https://github.com/asterinas/vostd/actions/workflows/ci.yml)
[![verify (verus-lang/verus)](https://img.shields.io/github/actions/workflow/status/asterinas/vostd/ci-upstream-verus.yml?branch=main&label=verify%20(verus-lang%2Fverus))](https://github.com/asterinas/vostd/actions/workflows/ci-upstream-verus.yml)

The `vostd` project provides a formally-verified version of [OSTD](https://asterinas.github.io/book/ostd/index.html), the (unofficial) standard library for OS development in safe Rust. OSTD encapsulates low-level hardware interactions—which requires using `unsafe` Rust—into a small yet powerful set of high-level, safe abstractions. These abstractions enable the creation of complex, general-purpose OSes like [Asterinas](https://github.com/asterinas/asterinas) entirely in safe Rust.

By design, OSTD guarantees *soundness*: no undefined behavior is possible, regardless of how its API is used in safe Rust. The goal of the `vostd` project is to bolster confidence in this soundness through formal verification, leveraging the [Verus](https://github.com/verus-lang/verus) verification tool.

This work is ongoing. Our current focus is on verifying OSTD’s *memory management subsystem*, a core component that is directly related to kernel memory safety. As we continue, we aim to extend formal verification to additional parts of OSTD to further ensure its reliability and correctness.

## Project Structure

Implementation code from the OSTD [mainline](https://github.com/asterinas/asterinas), together with its accompanying proofs, resides in the `ostd/src` directory, while specifications are located under `ostd/specs`.

This repository currently contains verification code for `ostd/src/mm` and `ostd/src/sync`. It is independent of the concurrency proofs presented in our [SOSP paper](https://dl.acm.org/doi/10.1145/3731569.3764836) — *“CortenMM: Efficient Memory Management with Strong Correctness Guarantees.”*  For the SOSP artifact, please refer to the [func-correct](https://github.com/asterinas/vostd/tree/func-correct) branch for verification code, and to [this repo](https://github.com/TELOS-syslab/CortenMM-Artifact) for the complete artifact.

A merge of these efforts is planned, but has not yet begun.

## Building the Proof Development

### Install Rust

If you have not installed Rust yet, follow the [official instructions](https://www.rust-lang.org/tools/install).

### Clone Submodule

`vostd` relies on our [custom build tool](https://github.com/asterinas/rust-deductive-verifier). Please run:

```bash
git submodule update --init --recursive
```

### Build Verus

The recommended way to build Verus is by running the following command:

```bash
make verus
```

or

```bash
cargo dv bootstrap
```

Verus should be automatically cloned and built in the `tools` directory. If download fails, please clone the repo manually into `tools/verus` , then run `cargo dv bootstrap` again.

> [!NOTE]
>
> We use [our own fork](https://github.com/asterinas/verus) of Verus, which we continuously synchronize with the upstream repository. You may choose to install the [upstream Verus source](https://github.com/verus-lang/verus) via `cargo dv bootstrap --upstream-verus`, however, we cannot guarantee that it will always verify successfully with our project. That said, our CI continuously tests against upstream, and we typically resolve any breaking changes within about a week.
>
> If you have already installed Verus elsewhere and just want to reproduce the verification result, a quick alternative is to set `CARGO_VERUS_PATH` to the directory containing the `cargo-verus` binary, or add it to your `PATH`. Then run `cargo verus verify`.

### Build Verification Targets

To verify the entire project, simply run:

```bash
make
```

or

```bash
cargo dv verify
```

To verify only `ostd` and skip its dependencies, run:

```bash
cargo dv verify -f --targets ostd
```

The `ostd` crate relies on a verified crate: `vstd_extra`. To verify it independently, run:

```bash
cargo dv verify --targets vstd_extra
```

### Clean Build Artifacts

Recompilation and reverification are automatically skipped for crates that have not changed since the last build. To remove the build artifact for a fresh build, run:

```bash
make clean
```

or

```bash
cargo dv clean
```

### Documentation

We provide comprehensive API-level documentation that describes the verified APIs along with their specifications. To generate the documentation, run:

```bash
make doc
```

or

```bash
cargo dv build
cargo dv doc --target ostd
```

The generated documentation can be found at `doc/index.html`. An [online version](https://asterinas.github.io/vostd/) is also available.

### IDE Support

For VSCode users, the [`verus-analyzer`](https://marketplace.visualstudio.com/items?itemName=verus-lang.verus-analyzer) extension is available in the Marketplace.

For Emacs users, please refer to the [`verus-mode`](https://github.com/verus-lang/verus-mode.el).

## Contributing to VOSTD

We welcome your contributions!

### Common Conventions

- We add an `axiom_` prefix to the name of each `axiom fn` and a `lemma_` prefix to each `proof fn`.
- We prefer associated functions to isolated lemmas.
- Specifications and lemmas are preferred to be add to `ostd/specs`.
- General definitions and lemmas should be add to `verified_libs/vstd_extra`.

### Tips

- During your development process, please frequently run `make verus-upgrade` or `cargo dv bootstrap --upgrade` to stay up-to-date with the [latest supported version](https://github.com/asterinas/verus) of Verus.
- Format checking is enforced, please format your code with `cargo dv fmt` before submission.
- If you are contributing to Verus, we recommend submitting pull requests to [the upstream repo](https://github.com/verus-lang/verus) rather than our fork, since we aim to minimize differences between them.
