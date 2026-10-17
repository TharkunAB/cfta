#!/usr/bin/env bash
set -euo pipefail
root=/home/tritlo/Code/mcfta
base="$root/lean/restart-evidence/20261017-computable-query-rank"
lean=/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
out=$(mktemp -d /tmp/numeric-fuel-reproduce.XXXXXX)
export LEAN_PATH="$root/lean/.lake/build/lib/lean"
"$lean" -Dlinter.all=true "$root/lean/MicroCFTA/IntersectNumericFuel.lean" > "$out/source.log" 2>&1
"$lean" -Dlinter.all=true "$base/numeric-fuel-public.lean" > "$out/public.log" 2>&1
"$lean" -Dlinter.all=true "$base/numeric-fuel-kernels.lean" > "$out/kernels.log" 2>&1
test ! -s "$out/source.log"
if rg -n 'error(\(|:)|warning:|sorryAx' "$out/public.log" "$out/kernels.log"; then
  exit 1
fi
python3 "$base/numeric-fuel-verify.py"
printf 'Fresh reproduction logs: %s\n' "$out"
