set -eu
control=$(cut -d: -f3 /proc/self/cgroup)
for key in memory.max memory.high memory.swap.max; do cat "/sys/fs/cgroup${control}/${key}"; done > /home/tritlo/Code/mcfta/lean/restart-evidence/20261017-normalized-callback-comparison/normalized-comparison-execution-direct-15.caps
exec /home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -Dlinter.all=true /home/tritlo/Code/mcfta/lean/restart-evidence/20261017-normalized-callback-comparison/normalized-comparison-execution-direct-15.source.lean
