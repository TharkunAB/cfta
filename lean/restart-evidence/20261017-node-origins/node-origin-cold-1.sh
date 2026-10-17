#!/bin/bash
set -euo pipefail
control=$(cut -d: -f3 /proc/self/cgroup)
for key in memory.max memory.high memory.swap.max; do
  printf '%s=' "$key"
  cat "/sys/fs/cgroup${control}/${key}"
done
cd /home/tritlo/Code/mcfta
exec nix-shell --run 'bash /home/tritlo/Code/mcfta/lean/restart-evidence/20261017-node-origins/node-origin-cold-1.worker.sh'
