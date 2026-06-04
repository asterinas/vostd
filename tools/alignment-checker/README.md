# Alignment Checker

`alignment-checker` checks whether the exec-code API delta between the current
repository and an anchor repository is fully declared by module verification
configuration files.

The checker is intentionally narrow:

- It checks exec function existence and signatures.
- It ignores function bodies.
- It ignores `proof fn`, `spec fn`, and other non-exec functions.
- It erases Verus spec fields and explicit `exec` mode from signatures.
- It ignores Verus ghost/tracked parameters, including `tracked`, `Tracked<T>`,
  and `Ghost<T>`.
- It rejects `[[verified]]` declarations that point to current functions with
  `#[verifier::external_body]`.

## Usage

Run the checker with a top-level input TOML:

```bash
cargo run -p alignment-checker -- -i tools/alignment-checker/template.toml
```

On success it prints a summary:

```text
Configuration consistency check passed: checked 2 modules, 391 declared entries, 469 actual deltas
```

On failure it reports all consistency errors before exiting with a non-zero
status.

## Top-Level Config

The top-level config selects the anchor revision and the modules to check.

```toml
[anchor]
git = "https://github.com/asterinas/asterinas.git"
tag = "v0.16.0"

[[modules]]
name = "mm"
path = "modules/mm.toml"
source = "../../ostd/src/mm"

[[modules]]
name = "rcu"
path = "modules/rcu.toml"
source = "../../ostd/src/sync/rcu"
```

Fields:

- `anchor.git`: Git repository used as the anchor.
- `anchor.tag`: tag, branch, or revision checked out from the anchor.
- `anchor.path`: optional subdirectory inside the anchor repository.
- `modules[].name`: display name used in diagnostics.
- `modules[].path`: module verification TOML.
- `modules[].source`: Rust source directory for the module. If omitted, the
  checker uses the directory containing `path`, which keeps the old
  in-module `verification.toml` layout working.

Module declaration files may be kept centrally under
`tools/alignment-checker/modules/`.

## Module Config

A module config declares every exec function existence/signature delta found
between current and anchor. Undeclared deltas are reported as errors.

Supported declaration sections:

### `[[verified]]`

Declares an exec API that is verified.

```toml
[[verified]]
name = "vm_space::VmSpace::cursor_mut"
type = "function"
how = "rewrite"
```

Rules:

- The current function must exist.
- The current function must not have `#[verifier::external_body]`.
- Without `how`, or with `how = "same-signature"`, the current and anchor
  signatures must match.
- With `how = "rewrite"`, a signature change is expected.
- A current-only added API may be `verified` only with `how = "rewrite"`.
- A removed API cannot be `verified`.

Use `anchor` when the API moved or changed owner/name, for example trait method
to inherent method:

```toml
[[verified]]
name = "tlb::TlbFlusher::new"
anchor = "tlb::TlbFlusher<G>::new"
type = "function"
how = "rewrite"
```

This consumes both the current added function and the anchor removed function.

### `[[unsupported]]`

Declares an intentionally unsupported exec API delta.

```toml
[[unsupported]]
name = "vm_space::VmSpace::activate"
type = "function"
reason = "lack-hardware-support"
```

`unsupported` allows added, removed, and signature-changed deltas. It also
supports `anchor` for renamed or moved APIs:

```toml
[[unsupported]]
name = "new::Api::name"
anchor = "old::Api::name"
type = "function"
reason = "other"
```

Supported reasons are:

- `lack-hardware-support`
- `unsafe-dependency`
- `external-dependency`
- `unsupported-abi`
- `unsupported-architecture`
- `not-applicable`
- `other`

### `[[planned]]`

Declares an exec API delta that is planned but not yet classified as verified or
unsupported.

```toml
[[planned]]
name = "frame::linked_list::LinkedList<M>::cursor_mut_at"
type = "function"
```

`planned` allows added, removed, and signature-changed deltas.

## Name Resolution

The checker resolves declaration names by:

1. Exact key match.
2. Suffix match.
3. Suffix match after stripping type generic arguments.

This lets short names work when they are unambiguous, while still preserving
generic owner names in the index to avoid collisions.

Impl methods use keys like:

```text
module::<Type<T> as Trait>::method
module::Type<T>::method
```

Trait declarations use keys like:

```text
module::Trait::method
```

## Current Module Files

The current generated module declaration files are:

- `tools/alignment-checker/modules/mm.toml`
- `tools/alignment-checker/modules/rcu.toml`

The example top-level config is:

- `tools/alignment-checker/template.toml`

## Development Checks

Useful local checks:

```bash
cargo check -p alignment-checker
cargo test -p alignment-checker
cargo run -p alignment-checker -- -i tools/alignment-checker/template.toml
```
