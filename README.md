# Formal Verification of Asterinas OSTD with Verus

The `vostd` project provides a formally-verified version of [OSTD](https://asterinas.github.io/book/ostd/index.html), the (unofficial) standard library for OS development in safe Rust. OSTD encapsulates low-level hardware interactions—which requires using `unsafe` Rust—into a small yet powerful set of high-level, safe abstractions. These abstractions enable the creation of complex, general-purpose OSes like [Asterinas](https://github.com/asterinas/asterinas) entirely in safe Rust.

By design, OSTD guarantees *soundness*: no undefined behavior is possible, regardless of how its API is used in safe Rust. The goal of the `vostd` project is to bolster confidence in this soundness through formal verification, leveraging the [Verus](https://github.com/verus-lang/verus) verification tool.

This work is ongoing. Our current focus is on verifying OSTD’s *memory management subsystem*, a core component that is directly related to kernel memory safety. As we continue, we aim to extend formal verification to additional parts of OSTD to further ensure its reliability and correctness.

## Verified Branch

*Verified* holds all the verification code. Implementation code from the OSTD mainline (accompanied with proofs) resides in the `aster_common` and `ostd` directories, while specifications are located in `specs`.

This repository currently contains verification code for `ostd/src/mm` and `ostd/src/boot/memory_region.rs`. It is independent of the concurrency proofs presented in our [SOSP paper](https://dl.acm.org/doi/10.1145/3731569.3764836) — *“CortenMM: Efficient Memory Management with Strong Correctness Guarantees.”* A merge of these efforts is planned but has not yet started.

## Building the Proof Development

#### Install Rust

If you have not installed Rust yet, follow the [official instructions](https://www.rust-lang.org/tools/install).

#### Clone Submodule

`vostd` relies on our [custom build tool](https://github.com/asterinas/rust-deductive-verifier), please run:

```
git submodule update --init --recursive
```

#### Build Verus

You can build Verus with the following command:

```
cargo dv bootstrap
```

Verus should be automatically cloned and built in the `tools` directory. If download fails, please clone the repo manually into `tools/verus` , then run `cargo dv bootstrap` again.

#### Build Verification Targets

To verify the entire project, simply run:

```
cargo dv verify --targets ostd
```

The `ostd` crate relies on two verified libraries: `vstd_extra` and `aster_common`. To compile and verify these libraries independently, run:

```
cargo dv compile --targets vstd_extra
cargo dv compile --targets aster_common
```

#### Clean Build Artifacts

`dv` automatically skips recompilation and reverification for libraries that have not changed since the last build. To remove all build artifacts and force a fresh build, run:

```
cargo dv clean --targets vstd_extra
cargo dv clean --targets aster_common
```

You can also run `cargo dv clean` to clean all artifacts at once.

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
-  Format checking is currently disabled due to instability in `verusfmt`, but we still recommend formatting your code with `verusfmt` before submission.
- If you are contributing to Verus, we recommend submitting pull requests to [the official repo](https://github.com/verus-lang/verus) rather than our fork, since we aim to minimize differences between them.
