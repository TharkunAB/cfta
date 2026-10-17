#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd -- "$here/../../.." && pwd)
cd "$repo/lean"
lean=/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
export LEAN_PATH=.lake/build/lib/lean
"$lean" -Dlinter.all=true -o /tmp/SourceRecursiveIntersectionInstructionProfile-reproduce.olean "$repo/lean/MicroCFTA/SourceRecursiveIntersectionInstructionProfile.lean"
"$lean" -Dlinter.all=true "$here/instruction-profile-public.lean"
"$lean" -Dlinter.all=true "$here/instruction-profile-kernels.lean"
python3 "$here/instruction-profile-verify.py"
