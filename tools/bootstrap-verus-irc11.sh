#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
verus_dir="$repo_root/tools/verus"
source_dir="$verus_dir/source"
vargo_manifest="$verus_dir/tools/vargo/Cargo.toml"
vargo_bin="$verus_dir/tools/vargo/target/release/vargo"

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

cargo build --release --manifest-path "$vargo_manifest"

# The IRC11 patch predates weak-memory in Vargo's build fingerprint, so force
# vstd to rebuild whenever this bootstrap path is invoked.
rm -f "$source_dir/target-verus/release/.vstd-fingerprint"

(
    cd "$source_dir"
    "$vargo_bin" build --release --features singular --vstd-weak-memory
    "$vargo_bin" build --release -p verusdoc
)

# This Verus revision places standalone package builds in Cargo's default
# target directory, while the current dv searches beside the Verus binary.
cp "$source_dir/target/release/verusdoc" "$source_dir/target-verus/release/verusdoc"

test -x "$source_dir/target-verus/release/verus"
test -x "$source_dir/target-verus/release/verusdoc"
test -f "$source_dir/target-verus/release/verus-root"
test -f "$source_dir/target-verus/release/vstd.vir"
