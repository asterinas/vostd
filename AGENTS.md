# Repository Guidelines

## Project Structure & Module Organization

This repository contains the Verus proof development for Asterinas OSTD. The auxiliary verified libraries are under `verified_libs/`. Core OSTD implementation and proofs live in `ostd/src/`; specifications live in `ostd/specs/`. The verification build system is in `dv`. `kernel`, `osdk`, `test`, and `docs` are not considered in the verification scope.

## Build, Test, and Development Commands

- `git submodule update --init --recursive`: initialize required submodules.
- `make verus` or `cargo dv bootstrap`: fetch and build the configured Verus toolchain under `tools/`.
- `make` or `cargo dv verify --targets ostd`: verify the main `ostd` target.
- `cargo dv verify --targets ostd -- --verify-only-module <module_path>`: verify only a specific module, for example `sync::rwlock`.
- `cargo dv compile --targets vstd_extra`: compile and verify the `vstd_extra` library independently.
- `make fmt`: format Verus/Rust sources using the project formatter.
- `make doc`: verify and generate API documentation in `doc/`.
- `make clean`: remove Cargo and generated documentation artifacts.

## Coding Style & Naming Conventions

Use Rust 2021 style with Verus proof conventions. Keep executable code, `spec` functions, proof blocks, and lemmas clearly separated so verification intent is visible in review. Name modules and files in `snake_case`; use `CamelCase` for types and traits, `SCREAMING_SNAKE_CASE` for constants, and descriptive lemma names such as `lemma_page_table_mapping_preserved`. Formatting follows `rustfmt.toml`: 4-space indentation, crate-level import grouping, and reordered imports. Public verified APIs should include rustdoc comments explaining both behavior and proof obligations. Suppress lints at the narrowest practical scope, preferably with `#[expect(...)]`.

## Verus Requirements

Before implementing proof-sensitive changes, read the relevant Verus Guide section and nearby project proofs. Prefer existing patterns from `ostd/specs/`, `verified_libs/`, and adjacent lemmas over inventing new proof structure. Make invariants explicit in specs, preconditions, postconditions, and lemma names. Compile and verify with Verus before submitting; fix verification failures rather than weakening specs to pass.

## Hard Constraints

- Do not change any code outside of the verification scope (e.g., `kernel/`, `osdk/`, `test/`, `docs/`).
- Do not modify any executable Rust code.
- Try to only change proof code first to fix verification issues, and only modify specifications if necessary to enable proofs.
- Keep edits minimal and localized to the smallest necessary dependency closure.

## Testing and Verification Guidelines

Verification is the primary correctness gate. Run `make` before submitting changes that affect `ostd`, `verified_libs`, or proof code. For targeted work on specific modules, use the `--verify-only-module` flag to speed up iteration.

## Commit & Pull Request Guidelines

Recent history uses short, imperative summaries but does not enforce a strict prefix convention. Prefer clear subjects such as `Fix page table cursor lemma`. Pull requests should describe the changed subsystem, list verification or formatting commands run and link related issues.

## Security & Configuration Tips

Do not commit generated artifacts such as `target/`, `doc/`, or local logs. Keep Verus, Z3, and bootstrap configuration local through environment variables such as `VERUS_PATH` and `VERUS_Z3_PATH` when needed.

## Verus References

- [Verus Guide](https://verus-lang.github.io/verus/guide/)
- [vstd Library](https://verus-lang.github.io/verus/verusdoc/vstd/)
