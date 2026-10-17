#!/usr/bin/env bash
set -euo pipefail
root=/home/tritlo/Code/mcfta
base="$root/lean/restart-evidence/20261017-native-instruction-budget"
lean=/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
out=$(mktemp -d /tmp/compile-cost-reproduce.XXXXXX)
export LEAN_PATH="$root/lean/.lake/build/lib/lean"
"$lean" -Dlinter.all=true "$root/lean/MicroCFTA/SourceRecursiveIntersectionCompileInstructionCredit.lean" > "$out/compile.log" 2>&1
"$lean" -Dlinter.all=true "$root/lean/MicroCFTA/SourceEqualityNativeCheckedInstructionCredit.lean" > "$out/checked.log" 2>&1
"$lean" -Dlinter.all=true "$base/compile-cost-public.lean" > "$out/public.log" 2>&1
"$lean" -Dlinter.all=true "$base/compile-cost-kernels.lean" > "$out/kernels.log" 2>&1
test ! -s "$out/compile.log"
test ! -s "$out/checked.log"
if rg -n 'error(\(|:)|warning:|sorryAx' "$out/public.log" "$out/kernels.log"; then
  exit 1
fi
python3 "$base/compile-cost-verify.py"
printf 'Fresh reproduction logs: %s\n' "$out"
