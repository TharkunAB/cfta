#!/usr/bin/env bash
set -eu
cd /home/tritlo/Code/mcfta/lean
export LEAN_PATH=.lake/build/lib/lean
lean_bin=/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
evidence=/home/tritlo/Code/mcfta/lean/restart-evidence/20261017-native-mass-resources
"$lean_bin" -Dlinter.all=true -o /tmp/checked-edge-mass-public-reproduced.olean "$evidence/checked-edge-mass-public.lean"
"$lean_bin" -Dlinter.all=true -o /tmp/checked-edge-mass-kernels-reproduced.olean "$evidence/checked-edge-mass-kernels.lean"
python3 "$evidence/checked-edge-mass-verify.py"
