#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd -- "$here/../../.." && pwd)
cd "$repo/lean"
export LEAN_PATH=.lake/build/lib/lean
lean=/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
"$lean" -Dlinter.all=true "$here/instruction-step-review-public.lean"
"$lean" -Dlinter.all=true "$here/instruction-step-review-kernels.lean"
python3 "$here/instruction-step-review-verify.py"
