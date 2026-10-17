#!/usr/bin/env bash
set -eu
root=/home/tritlo/Code/mcfta
base="$root/lean/restart-evidence/20261017-native-width-producer"
output=$(mktemp -d /tmp/mcfta-width-trace-review.XXXXXX)
for component in public kernels; do
  LEAN_PATH="$root/lean/.lake/build/lib/lean" \
    /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -Dlinter.all=true \
    "$base/width-trace-review-$component.lean" > "$output/$component.log" 2>&1
  if rg -n 'error(\(|:)|warning:|sorryAx' "$output/$component.log"; then
    exit 1
  fi
done
python3 "$base/width-trace-review-verify.py"
echo "$output"
