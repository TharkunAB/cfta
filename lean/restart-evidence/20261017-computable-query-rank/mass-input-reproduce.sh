#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd -- "$here/../../.." && pwd)
cd "$repo/lean"
export LEAN_PATH=.lake/build/lib/lean
lean=/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
"$lean" -Dlinter.all=true -o /tmp/SourceRecursiveIntersectionMassInputBounds-reproduce.olean "$repo/lean/MicroCFTA/SourceRecursiveIntersectionMassInputBounds.lean"
"$lean" -Dlinter.all=true "$here/mass-input-public.lean"
"$lean" -Dlinter.all=true "$here/mass-input-kernels.lean"
python3 "$here/mass-input-verify.py"
