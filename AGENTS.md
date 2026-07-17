# Repository Guidelines

## Project Structure & Module Organization

This repository contains the Verus proof development for Asterinas OSTD. The layout is given as follows:

- `verified_libs/`: The auxiliary verified libraries.
- `ostd`:
  - `ostd/src/`: Core OSTD implementation and proofs.
  - `ostd/specs/`: Verus specifications for OSTD.
- `dv`: The main build system (you can think this as `xtask`-equivalent).

Other components like `kernel` and `osdk` shall be ignored during verification.

## Build, Test, and Development Commands

- `git submodule update --init --recursive`: initialize required submodules.
- `make verus` or `cargo dv bootstrap`: fetch and build the configured Verus toolchain under `tools/`.
  - `make verus update` or `cargo dv bootstrap --upgrade`: needed if there is compilation errors which might be caused by toolchain updates.
- `make` or `cargo dv verify`: verify the whole target.
- `cargo dv verify --targets ostd -- --verify-only-module <module_path>`: verify only a specific module, for example `sync::rwlock`.
- `cargo dv verify --targets vstd_extra`: compile and verify the `vstd_extra` library independently.
- `make fmt`: format Verus/Rust sources using the project formatter.
- `make doc`: verify and generate API documentation in `doc/`.
- `make clean`: remove Cargo and generated documentation artifacts.

## Coding Style & Naming Conventions

- Use Rust 2021 style with Verus proof conventions.
- Keep executable code, `spec` functions, proof blocks, and lemmas clearly separated so verification intent is visible in review.
- Name modules and files in `snake_case`; use `CamelCase` for types and traits, `SCREAMING_SNAKE_CASE` for constants, prefix proof lemmas using `lemma_` like `lemma_page_table_mapping_preserved`, prefix axioms using `axiom_`, and prefix `tracked_` for helper functions that lift verus functions that return ghost types into `tracked`.
- Formatting follows `rustfmt.toml`: 4-space indentation, crate-level import grouping, and reordered imports.
- Public verified APIs should include rustdoc comments explaining both behavior and proof obligations. Suppress lints at the narrowest practical scope, preferably with `#[expect(...)]`.
- Whenever there is proof-only objects inside executable Rust types, be sure to add prefixes to the variables. Example:
  ```rs
  pub struct Foo {
      something: u64,
      tracked_thing: Tracked<u8>,
      //             ^^^^^^^
      ghost_another: Ghost<u32>,
      //             ^^^^^
  }
  ```

## Verus Requirements

For proof-sensitive changes, use Verus-related skills in `.agents/skills` only when nontrivial Verus reasoning, specification changes, or verification failures require it. Keep routine edits lightweight.

## Hard Constraints

- Do not change any code outside of the verification scope (e.g., `kernel/`, `osdk/`).
- Try to only change proof code first to fix verification issues, and only modify specifications if necessary to enable proofs.
- Avoid changing executable Rust code unless required to support verification (e.g., use `PPtr` instead of raw pointers). All changes to executable code must be prompted to the user or justified in the PR description, and should not change observable behavior.
- Keep edits minimal and localized to the smallest necessary dependency closure.
- Never add `#[verifier::external_body]`, `admit()`, or `assume()` unless instructed. If you really need to add them, prompt the user first to see if adding cheating code is necessary.

## Testing and Verification Guidelines

Verification is the primary correctness gate. Run `make` before submitting changes that affect `ostd`, `verified_libs`, or proof code. For targeted work on specific modules, use the `--verify-only-module` flag to speed up iteration.

## Commit & Pull Request Guidelines

Recent history uses short, imperative summaries but does not enforce a strict prefix convention. Prefer clear subjects such as `Fix page table cursor lemma`. Pull requests should describe the changed subsystem, list verification or formatting commands run and link related issues.

## Security & Configuration Tips

Do not commit generated artifacts such as `target/`, `doc/`, or local logs. To point the build at a locally installed Verus instead of the one bootstrapped under `tools/verus`, set `CARGO_VERUS_PATH` to the directory containing the `cargo-verus` binary (or add it to `PATH`).
