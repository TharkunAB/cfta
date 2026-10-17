#!/bin/bash
set -eu
control=$(cut -d: -f3 /proc/self/cgroup)
for key in memory.max memory.high memory.swap.max; do cat "/sys/fs/cgroup${control}/${key}"; done > /home/tritlo/Code/mcfta/lean/restart-evidence/20261017-node-origins/callback-erasure-kernels-1.caps
export LEAN_PATH=/home/tritlo/Code/mcfta/lean/.lake/build/lib/lean
exec /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -Dlinter.all=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261017-node-origins/callback-erasure-kernels-1.source.lean
