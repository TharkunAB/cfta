#!/usr/bin/env bash
set -eu
cd /home/tritlo/Code/mcfta/lean
export LEAN_PATH=.lake/build/lib/lean
lean_bin=/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean
evidence=/home/tritlo/Code/mcfta/lean/restart-evidence/20261017-causal-result-mass
"$lean_bin" -Dlinter.all=true -o /tmp/root-mass-width-uniform-public-reproduced.olean "$evidence/root-mass-width-uniform-public.lean"
"$lean_bin" -Dlinter.all=true -o /tmp/root-mass-width-uniform-kernels-reproduced.olean "$evidence/root-mass-width-uniform-kernels.lean"
python3 "$evidence/root-mass-width-uniform-verify.py"
