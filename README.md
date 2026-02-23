# Formal Verification of Asterinas OSTD with Verus

The `vostd` project provides a formally-verified version of [OSTD](https://asterinas.github.io/book/ostd/index.html), the (unofficial) standard library for OS development in safe Rust. OSTD encapsulates low-level hardware interactions—which requires using `unsafe` Rust—into a small yet powerful set of high-level, safe abstractions. These abstractions enable the creation of complex, general-purpose OSes like [Asterinas](https://github.com/asterinas/asterinas) entirely in safe Rust.

By design, OSTD guarantees *soundness*: no undefined behavior is possible, regardless of how its API is used in safe Rust. The goal of the `vostd` project is to bolster confidence in this soundness through formal verification, leveraging the [Verus](https://github.com/verus-lang/verus) verification tool.

This work is ongoing. Our current focus is on verifying OSTD’s *memory management subsystem*, a core component that is directly related to kernel memory safety. As we continue, we aim to extend formal verification to additional parts of OSTD to further ensure its reliability and correctness.

## Project Structure

Implementation code from the OSTD [mainline](https://github.com/asterinas/asterinas), together with its accompanying proofs, resides in the `aster_common` and `ostd` directories, while specifications are located under `specs`.

This repository currently contains verification code for `ostd/src/mm` and `ostd/src/sync`. It is independent of the concurrency proofs presented in our [SOSP paper](https://dl.acm.org/doi/10.1145/3731569.3764836) — *“CortenMM: Efficient Memory Management with Strong Correctness Guarantees.”*  For the SOSP artifact, please refer to the [func-correct](https://github.com/asterinas/vostd/tree/func-correct) branch for verification code, and to [this repo](https://github.com/TELOS-syslab/CortenMM-Artifact) for the complete artifact.

A merge of these efforts is planned, but has not yet begun.

## Building the Proof Development

#### Install Rust

If you have not installed Rust yet, follow the [official instructions](https://www.rust-lang.org/tools/install).

#### Clone Submodule

`vostd` relies on our [custom build tool](https://github.com/asterinas/rust-deductive-verifier). Please run:

```
git submodule update --init --recursive
```

#### Build Verus

You can build Verus with the following command:

```
cargo dv bootstrap
```

Verus should be automatically cloned and built in the `tools` directory. If download fails, please clone the repo manually into `tools/verus` , then run `cargo dv bootstrap` again.

We utilize [our own fork](https://github.com/asterinas/verus) of Verus, which we continuously synchronize with the official repository. While you may manually clone the [official Verus source](https://github.com/verus-lang/verus), please note that we cannot guarantee it will compile correctly. (We typically address any breaking changes within a week.)


#### Build Verification Targets

To verify the entire project, simply run:

```
cargo dv verify --targets ostd
```

The `ostd` crate relies on a verified library: `vstd_extra`. To compile and verify the library independently, run:

```
cargo dv compile --targets vstd_extra
```

#### Clean Build Artifacts

`dv` automatically skips recompilation and reverification for libraries that have not changed since the last build. To remove the build artifact of a particular library and force a fresh build, run:

```
cargo dv clean --targets vstd_extra
```

You can also run `cargo dv clean` to clean all artifacts at once.

#### Documentation

We provide comprehensive API-level documentation that describes the verified APIs along with their auxiliary lemmas. To generate the documentation, run:

```
cargo dv doc --target ostd
```

The generated documentation can be found at `doc/index.html`. An online version is also available [here](https://asterinas.github.io/vostd/).

#### IDE Support

For VSCode users, the [`verus-analyzer`](https://marketplace.visualstudio.com/items?itemName=verus-lang.verus-analyzer) extension is available in the Marketplace.

For Emacs users, please refer to the [`verus-mode`](https://github.com/verus-lang/verus-mode.el).

## Contributing to VOSTD

We welcome your contributions!

#### Common Conventions

- We add an `axiom_` prefix to the name of each `axiom fn` and a `lemma_` prefix to each `proof fn`.
- We prefer associated functions to isolated lemmas.

#### Tips

- During your development process, please frequently run `cargo dv bootstrap --upgrade` to stay up-to-date with the [latest supported version](https://github.com/asterinas/verus) of Verus.
-  Format checking is not enforced, but we still recommend formatting your code with `cargo dv fmt --paths path_to_your_file` before submission.
- If you are contributing to Verus, we recommend submitting pull requests to [the official repo](https://github.com/verus-lang/verus) rather than our fork, since we aim to minimize differences between them.
