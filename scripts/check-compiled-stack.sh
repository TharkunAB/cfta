#!/usr/bin/env bash
set -euo pipefail

if (( $# > 1 )); then
    echo "usage: $0 [compiled-stack.tsv]" >&2
    exit 2
fi

root=$(cd "$(dirname "$0")/.." && pwd)
proof=$(mktemp -d)
trap 'rm -rf "$proof"' EXIT
if (( $# == 1 )); then
    cp -- "$1" "$proof/compiled-stack.tsv"
else
    cd "$root"
    target=cfta-generator:bench:state-machine-trace-speed
    cabal build "$target"
    exporter=$(cabal list-bin "$target")
    "$exporter" compiled-stack > "$proof/compiled-stack.tsv"
fi

cp "$root"/docs/proofs/{IndexedTrace,CompiledStack}.lean "$proof/"
cd "$proof"
toolchain=+leanprover/lean4:v4.26.0
lean "$toolchain" -o IndexedTrace.olean IndexedTrace.lean
LEAN_PATH="$proof" lean "$toolchain" "$proof/CompiledStack.lean"
echo "Lean verified the compiled stack table and every rank through length two."
