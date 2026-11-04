#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
verus_dir="$repo_root/tools/verus"
source_dir="$verus_dir/source"
target_dir="$source_dir/target-verus"
release_dir="$target_dir/release"

if [[ ! -f "$source_dir/vstd/atomic_weak.rs" ]]; then
    echo "The pinned Verus checkout does not contain IRC11 support" >&2
    exit 1
fi

if [[ ! -x "$source_dir/z3" ]]; then
    (
        cd "$source_dir"
        ./tools/get-z3.sh
    )
fi

(
    cd "$source_dir"
    cargo build --release --target-dir "$target_dir" \
        -p rust_verify -p verus -p cargo-verus -p verusdoc \
    "$release_dir/cargo-verus" build --release --target-dir "$target_dir" \
        --manifest-path vstd/Cargo.toml --features weak-memory
)

# Keep standalone verification able to find Z3 beside the Verus executable.
cp "$source_dir/z3" "$release_dir/z3"

test -x "$source_dir/target-verus/release/verus"
test -x "$source_dir/target-verus/release/verusdoc"
test -f "$source_dir/target-verus/release/vstd.vir"
