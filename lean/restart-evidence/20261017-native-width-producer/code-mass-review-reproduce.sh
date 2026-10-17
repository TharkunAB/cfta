#!/usr/bin/env bash
set -eu
cd /home/tritlo/Code/mcfta/lean
export LEAN_PATH=.lake/build/lib/lean
lean_bin=/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
evidence=/home/tritlo/Code/mcfta/lean/restart-evidence/20261017-native-width-producer
"$lean_bin" -Dlinter.all=true -o /tmp/code-mass-review-public-reproduced.olean "$evidence/code-mass-review-public.lean"
"$lean_bin" -Dlinter.all=true -o /tmp/code-mass-review-kernels-reproduced.olean "$evidence/code-mass-review-kernels.lean"
python3 "$evidence/code-mass-review-verify.py"
